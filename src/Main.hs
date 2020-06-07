{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wall -Wno-orphans #-}

module Main where

import Control.Applicative
import Control.Exception
import Control.Monad
import Control.Monad.Except
import Control.Unification
import Control.Unification.IntVar
import Data.Coerce
import Data.Function
import Data.Functor.Identity
import Data.List
import Data.Maybe
import Data.String
import DynFlags
import GHC
import GHC.IO.Exception
import GHC.Paths (libdir)
import GHC.SourceGen
import GHC.Stack (HasCallStack)
import Optics hiding (cons, elements)
import System.IO
import System.Process
import Test.QuickCheck
import Test.QuickCheck.Gen
import Test.QuickCheck.Random

import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import qualified Data.Set as Set


--------------------------------------------------------------------------------
-- Universe of Types/Kinds
--------------------------------------------------------------------------------

-- | A type scheme, since we don't have higher-rank polymorphism or
-- impredicativity.
data PolyUniverse = U_Forall [(IntVar, (OccNameStr, UniverseKind))] Universe
  deriving Show

type UPolyType = PolyUniverse

type Universe     = UTerm UniverseF IntVar
type UniverseKind = Universe
type UniverseType = Universe

-- | Functor whose fixed point is the universe of types/kinds.
data UniverseF t
    = Un_Type  -- ^ the kind Type of types
    | Un_ADT OccNameStr
    | Un_Int
    | Un_Arr
    | Un_App t t
    | Un_Skolem OccNameStr
      -- ^ Named Skolem variable, used when generating polymorphic functions
  deriving (Functor, Foldable, Traversable, Eq, Show)

instance Unifiable UniverseF where
  zipMatch :: UniverseF a -> UniverseF a -> Maybe (UniverseF (Either a (a,a)))
  zipMatch Un_Type       Un_Type       = Just Un_Type
  zipMatch (Un_ADT n)    (Un_ADT n')   | n == n' = Just (Un_ADT n)
  zipMatch Un_Int        Un_Int        = Just Un_Int
  zipMatch Un_Arr        Un_Arr        = Just Un_Arr
  zipMatch (Un_App a b)  (Un_App c d)  = Just (Un_App (Right (a,c)) (Right (b,d)))
  zipMatch (Un_Skolem x) (Un_Skolem y) | x == y = Just (Un_Skolem x)
  zipMatch _               _           = Nothing


pattern U_Mono :: Universe -> PolyUniverse
pattern U_Mono u = U_Forall [] u


pattern U_Type :: UniverseKind
pattern U_Type = UTerm Un_Type

pattern U_Int :: Universe
pattern U_Int = UTerm Un_Int

pattern U_ADT :: OccNameStr -> Universe
pattern U_ADT n = UTerm (Un_ADT n)

pattern U_ADT1 :: OccNameStr -> Universe -> Universe
pattern U_ADT1 n t = U_ADT n :$: t

pattern U_ADT2 :: OccNameStr -> Universe -> Universe -> Universe
pattern U_ADT2 n s t = (U_ADT n :$: s) :$: t

pattern U_Unit :: Universe
pattern U_Unit = U_ADT "()"

pattern U_Pair :: Universe -> Universe -> Universe
pattern U_Pair s t = U_ADT2 "(,)" s t

pattern U_Either :: Universe -> Universe -> Universe
pattern U_Either s t = U_ADT2 "Either" s t

pattern U_Maybe :: Universe -> Universe
pattern U_Maybe t = U_ADT1 "Maybe" t

pattern U_Bool :: Universe
pattern U_Bool = U_ADT "Bool"

pattern U_List :: Universe -> Universe
pattern U_List t = U_ADT1 "[]" t

pattern U_Arr :: Universe
pattern U_Arr = UTerm Un_Arr

pattern (:->:) :: Universe -> Universe -> Universe
pattern (:->:) s t = (U_Arr :$: s) :$: t
infixr 0 :->:

pattern (:$:) :: Universe -> Universe -> Universe
pattern (:$:) s t = UTerm (Un_App s t)
infixl 0 :$:

pattern U_Skolem :: OccNameStr -> Universe
pattern U_Skolem x = UTerm (Un_Skolem x)

{-# COMPLETE U_Type, U_ADT, U_Int, U_Arr, (:$:), U_Skolem, UVar #-}


varsMap :: [(IntVar, (OccNameStr, UniverseKind))]
        -> IntMap.IntMap (OccNameStr, UniverseKind)
varsMap = IntMap.fromList . coerce

lookupVarName :: IntVar -> IntMap.IntMap (OccNameStr, UniverseKind) -> OccNameStr
lookupVarName (IntVar v) m = fst (m IntMap.! v)

lookupVarKind :: IntVar -> IntMap.IntMap (OccNameStr, UniverseKind) -> UniverseKind
lookupVarKind (IntVar v) m = snd (m IntMap.! v)


-- | Translate a type scheme into the actual syntax of types.
elPoly :: PolyUniverse -> HsType'
elPoly (U_Forall as t) = el (varsMap as) t

-- | Translate a type in the universe into the actual syntax of types.  This
-- uses a mapping from unification variables to their names, which must have an
-- entry for every free 'UVar'.
el :: IntMap.IntMap (OccNameStr, UniverseKind) -> Universe -> HsType'
el m (UVar v)     = bvar $ lookupVarName v m
el _ (U_Skolem x) = var (UnqualStr x)
el _ U_Type       = var "Type"
el m (U_List u)   = listTy (el m u)
el m (U_Pair s t) = tuple [el m s, el m t]
el _ (U_ADT n)    = var (UnqualStr n)
el _ U_Int        = var "Int"
el m (u :->: v)   = el m u --> el m v
el m (u :$: v)    = el m u @@ el m v
el _ U_Arr        = var "(->)"


--------------------------------------------------------------------------------
-- Contexts
--------------------------------------------------------------------------------

data Context =
  Context { _context_terms :: Map.Map OccNameStr (Frequency, UPolyType)
            -- ^ Term variables in scope, with their types and a frequency with
            -- which to pick them when choosing a variable to apply. This
            -- conflates global and local definitions.
          , _context_types :: IntMap.IntMap (OccNameStr, UniverseKind)
            -- ^ Type variables in scope, with their kinds.
          , _context_adts :: ADTMap
            -- ^ Map from ADT name to its details.
          }
  deriving Show

type Frequency = Int

-- | Map from ADT name to its arity and the names and types of its constructors.
-- Invariant: UPolyType must end in the appropriate U_ADT<n> type
type ADTMap = Map.Map OccNameStr (UniverseKind, [(OccNameStr, UPolyType)])

instance Semigroup Context where
  cx1 <> cx2 = Context { _context_terms = _context_terms cx1 <> _context_terms cx2
                       , _context_types = _context_types cx1 <> _context_types cx2
                       , _context_adts  = _context_adts cx1 <> _context_adts cx2
                       }

instance Monoid Context where
  mempty = Context mempty mempty mempty


$(makeLenses ''Context)


-- | Add a term binding to the context.  This shadows any existing binding with
-- the same name, so we don't accidentally try to use it and end up with a type
-- error.
withTerm :: Context -> (OccNameStr, (Frequency, Universe)) -> Context
withTerm cx (a,(freq,u)) = cx & context_terms %~ Map.insert a (freq, U_Mono u)

withTerms :: Context -> [(OccNameStr, (Frequency, Universe))] -> Context
withTerms cx as = withPolyTerms cx (map (fmap (fmap U_Mono)) as)

withPolyTerms :: Context -> [(OccNameStr, (Frequency, PolyUniverse))] -> Context
withPolyTerms cx as = cx & context_terms %~ Map.union (Map.fromList as)

withTypes :: Context-> [(IntVar, (OccNameStr, UniverseKind))] -> Context
withTypes cx as = cx { _context_types = varsMap as <> _context_types cx }


--------------------------------------------------------------------------------
-- Generating Types
-------------------------------------------------------------------------------

genPolyType :: Context -> Gen PolyUniverse
genPolyType cx = do
    binds <- genTyVarBinds
    U_Forall binds <$> genTypeType (cx `withTypes` binds) `suchThat` (not . boring)
    -- TODO: strip out unused tyvar binds?
  where
    -- Don't generate @forall a . a@, because it will inevitably be bound to a
    -- loop, and if we have it in the context then many definitions end up
    -- trying to use it because it is always applicable.
    boring UVar{} = True
    boring _      = False

genTyVarBinds :: Gen [(IntVar, (OccNameStr, UniverseKind))]
genTyVarBinds = do
    n <- choose (0, 2)
    smaller $ zipWith f [0..] <$> (vectorOf n ((,) <$> tyVarName <*> genKind))
  where
    f i (a, k) = (IntVar i, (a, k))

genTypeType :: Context -> Gen UniverseType
genTypeType cx = genType cx U_Type

genType :: Context -> UniverseKind -> Gen UniverseType
genType cx@Context{..} kind@U_Type = sized $ \sz ->
    frequency $
    [ (3, pure U_Int)
    , (sz, (:->:) <$> smaller (genTypeType cx) <*> genTypeType cx) -- TODO smaller!
    ] ++ tyvars
      ++ adts
  where
    tyvars = [ (5, UVar <$> elements applicable_tyvars)
             | not (null applicable_tyvars) ]
    applicable_tyvars = [ IntVar i
                        | (i, (_, k)) <- IntMap.toList _context_types
                        , k `eqUniverse` kind
                        ]
    adts = [ (3, gen)
           | (adt, (adt_kind, _)) <- Map.toList _context_adts
           , Just gen <- [genADT cx adt adt_kind]
           ]

genType _cx _kind = error "genType: TODO: generate types of non-Type kinds"

genADT :: Context -> OccNameStr -> UniverseKind -> Maybe (Gen UniverseType)
genADT cx adt kind = do
  gen_kinds <- applicable cx U_Type (U_Mono kind)
  pure $ foldl (:$:) (U_ADT adt) <$> smaller (mapM (genType cx) =<< gen_kinds)

genKind :: Gen UniverseKind
genKind = frequency [ (3, pure U_Type)
                    , (1, (:->:) <$> genKind <*> genKind) -- TODO: smaller!
                    ]


--------------------------------------------------------------------------------
-- Generating Expressions
--------------------------------------------------------------------------------

genExpr :: Context -> Universe -> Gen HsExpr'
genExpr cx u = sized $ \sz -> frequency [ (sz `div` 5, genNeutralExpr cx u)
                                        , (3, genCanonicalExpr cx u)
                                        ]

genCanonicalExpr :: Context -> Universe -> Gen HsExpr'
genCanonicalExpr _  U_Skolem{} = pure $ var "undefined"
genCanonicalExpr _  U_Int      = int <$> arbitrary
genCanonicalExpr cx (U_List u) = genListExpr cx u
genCanonicalExpr cx (u :->: v) = genLambdaExpr cx u v
genCanonicalExpr cx u@(U_ADT n)      = genDataConExpr cx n u
genCanonicalExpr cx u@(U_ADT1 n _)   = genDataConExpr cx n u
genCanonicalExpr cx u@(U_ADT2 n _ _) = genDataConExpr cx n u
genCanonicalExpr _  (_ :$: _) = pure $ var "undefined" -- TODO
genCanonicalExpr _  U_Arr = error "genCanonicalExpr: Arr is not of kind Type"
genCanonicalExpr _  U_Type = error "genCanonicalExpr: no terms have type Type"
genCanonicalExpr _  UVar{} = error "genCanonicalExpr: unification variable"

-- | Generate a lambda-term of type @u -> v@.
genLambdaExpr :: Context -> Universe -> Universe -> Gen HsExpr'
genLambdaExpr cx u v = do
    n <- lambdaVarName
    lambda [bvar n] <$> genExpr (cx `withTerm` (n,(100,u))) v

-- | Generate an expression of type @[u]@.
genListExpr :: Context -> Universe -> Gen HsExpr'
genListExpr cx u =
    frequency $ [ (5, pure nil)
                , (1, smaller $ (\x xs -> cons @@ x @@ xs)
                                  <$> genExpr cx u
                                  <*> genExpr cx (U_List u))
                , (20, smaller $ list <$> listOf (genExpr cx u))
                ] ++ enumerations
  where
    -- TODO: can lead to -Wempty-enumerations warnings
    enumerations = case u of
        U_Int -> [ (3, from       <$> genExpr cx u)
                 , (3, fromThen   <$> genExpr cx u <*> genExpr cx u)
                 , (3, fromTo     <$> genExpr cx u <*> genExpr cx u)
                 , (3, fromThenTo <$> genExpr cx u <*> genExpr cx u <*> genExpr cx u)
                 ]
        _      -> []

-- | Generate an expression of type @u@ by applying a data constructor, where
-- @u@ is an ADT called @n@.
genDataConExpr :: Context -> OccNameStr -> UniverseType -> Gen HsExpr'
genDataConExpr cx n u
  | null gens = error $ "genDataConExpr: could not generate " ++ show n
                          ++ " " ++ show (el mempty u)
                          ++ " from " ++ show (snd (_context_adts cx Map.! n))
  | otherwise = oneof gens
  where
    gens = [ (var (UnqualStr c) @@@) <$> (mapM (genExpr cx) =<< gen_arg_tys)
           | (c, ty) <- snd (_context_adts cx Map.! n)
           , Just gen_arg_tys <- [applicable cx u ty]
           ]

-- TODO: generate partially applied DataCons; treat them like variables?


genNeutralExpr :: Context -> Universe -> Gen HsExpr'
genNeutralExpr cx u =
    frequency [ (10, genApplicationExpr cx u)
              , (2, genCaseExpr cx u)
              , (2, genIfExpr cx u)
              , (1, genTypeConstraintExpr cx u)
              ]

genApplicationExpr :: Context -> Universe -> Gen HsExpr'
genApplicationExpr cx u
  | null apps = genCanonicalExpr cx u
  | otherwise = smaller $ frequency apps
  where
    apps :: [(Frequency, Gen HsExpr')]
    apps = [ (freq, (var (UnqualStr v) @@@) <$> (mapM (genExpr cx) =<< gen_arg_tys))
           | (v, (freq, u')) <- Map.toList (_context_terms cx)
           , Just gen_arg_tys <- [applicable cx u u']
           ]

-- | Generate a case expression by picking an arbitrary scrutinee type from the
-- known ADTs, generating an expression of that type, and for each constructor
-- generating a case branch.
genCaseExpr :: Context -> Universe -> Gen HsExpr'
genCaseExpr cx u = do
    (adt, (arity, constructors)) <- elements (Map.toList (_context_adts cx))
    scrutinee_type <- fromJust $ genADT cx adt arity
    smaller $ case' <$> genScrutineeExpr cx scrutinee_type
                    <*> (catMaybes <$> mapM (mkCon scrutinee_type) constructors)
  where
    -- In principle genExpr is allowed, but we prefer not to generate
    -- case (case ...), and case (Con ...) leads to overlapping-patterns warnings
    genScrutineeExpr = genApplicationExpr

    mkCon scrutinee_type (con, con_scheme) =
        forM (applicable cx scrutinee_type con_scheme) $ \gen_tys -> do
            tys <- gen_tys
            patbinds <- uniqueNames patVarName (map ((,) 1) tys)
            match [conP (UnqualStr con) (map (bvar . fst) patbinds)]
                      <$> genExpr (cx `withTerms` patbinds) u


-- | Generate an if-then-else expression.
genIfExpr :: Context -> UniverseType -> Gen HsExpr'
genIfExpr cx u =
    smaller $ if' <$> genExpr cx U_Bool <*> genExpr cx u <*> genExpr cx u


-- | Generate a type constraint on an expression.
--
-- TODO: the inner parentheses are sometimes necessary to avoid parse errors,
-- but not always, and it would be nice not to generate them when unneeded.
--
-- TODO: this can lead to type errors when the target type contains type
-- variables....
genTypeConstraintExpr :: Context -> UniverseType -> Gen HsExpr'
genTypeConstraintExpr cx u =
    smaller $ ((@::@) <$> (par <$> genExpr cx u) <*> pure (el mempty u))


--------------------------------------------------------------------------------
-- Generating Declarations and Modules
--------------------------------------------------------------------------------

genModule :: Gen HsModule'
genModule = do
    local_terms <- genTermTypes prelude
    let context = prelude `withPolyTerms` local_terms
    decls <- concat <$> mapM (genDecl context) local_terms
    exports <- oneof [pure Nothing
                     , Just . map (var . UnqualStr . fst) <$> sublistOf local_terms]
    let imports = []
    module' (Just "M") <$> pure exports <*> pure imports <*> pure decls

genTermTypes :: Context -> Gen [(OccNameStr, (Frequency, PolyUniverse))]
genTermTypes cx = uniqueNames varName . map ((,) 1) =<< listOf (genPolyType cx)

genDecl :: Context -> (OccNameStr, (Frequency, UPolyType)) -> Gen [HsDecl']
genDecl cx (n, (_, f@(U_Forall as u))) = do
    val <- genExpr cx (substitute [(i,U_Skolem a) | (i, (a, _)) <- as] u)
    pure [typeSig n (elPoly f), valBind n val]


--------------------------------------------------------------------------------
-- Prelude
--------------------------------------------------------------------------------

-- TODO: some of these are specialisations of their Prelude types, so we can end
-- up with ambiguity. Support type classes?
prelude :: Context
prelude = Context
  { _context_terms = Map.fromList $ map (\ (x,u) -> (x, (1, u)))
    [ ("+", U_Mono $ U_Int :->: U_Int :->: U_Int)
    , ("-", U_Mono $ U_Int :->: U_Int :->: U_Int)
    , ("*", U_Mono $ U_Int :->: U_Int :->: U_Int)
    , ("not", U_Mono $ U_Bool :->: U_Bool)
    , ("&&", U_Mono $ U_Bool :->: U_Bool :->: U_Bool)
    , ("||", U_Mono $ U_Bool :->: U_Bool :->: U_Bool)
    , ("map", U_Forall [a_, b_] $
                  (a :->: b) :->: U_List a :->: U_List b)
    -- , ("null", U_Forall [a_] $ U_List a :->: U_Bool)
    -- Foldable often leads to ambiguity if we include this
    , ("id", U_Forall [a_] (a :->: a))
    , ("otherwise", U_Mono U_Bool)
    , ("fst", U_Forall [a_, b_] (U_Pair a b :->: a))
    , ("snd", U_Forall [a_, b_] (U_Pair a b :->: b))
    , ("==", U_Mono $ U_Int :->: U_Int :->: U_Bool)
    , ("++", U_Forall [a_] (U_List a :->: U_List a :->: U_List a))
    ]
  , _context_types = mempty
  , _context_adts = Map.fromList
     [ ("Bool"  , ( U_Type
                  , [ ("True" , U_Mono U_Bool)
                    , ("False", U_Mono U_Bool)
                    ]))
     , ("Maybe" , ( U_Type :->: U_Type
                  , [ ("Nothing", U_Forall [a_] (       U_Maybe a))
                    , ("Just"   , U_Forall [a_] (a :->: U_Maybe a))
                    ]))
     , ("Either", ( U_Type :->: U_Type :->: U_Type
                  , [ ("Left" , U_Forall [a_, b_] (a :->: U_Either a b))
                    , ("Right", U_Forall [a_, b_] (b :->: U_Either a b))
                    ]))
     , ("(,)"   , ( U_Type :->: U_Type :->: U_Type
                  , [ ("(,)", U_Forall [a_, b_] (a :->: b :->: U_Pair a b)) ]))
     , ("()"    , ( U_Type
                  , [ ("()" , U_Mono U_Unit) ]))
     , ("[]"    , ( U_Type :->: U_Type
                  , [ ("[]" , U_Forall [a_] (                     U_List a))
                    , (":"  , U_Forall [a_] (a :->: U_List a :->: U_List a))
                    ]))
     ]
  }
  where
    a = UVar (IntVar 0)
    a_ = (IntVar 0, ("a", U_Type))
    b = UVar (IntVar 1)
    b_ = (IntVar 1, ("b", U_Type))


--------------------------------------------------------------------------------
-- Unification
--------------------------------------------------------------------------------

-- | Equality test on 'Universe', with metavariables equal only to themselves.
--
-- This should be equivalent to the (==) derived by
--     deriving instance (Eq v, Eq (t (UTerm t v))) => Eq (UTerm t v)
-- only without the orphan instance.
--
-- TODO: does unification-fd provide this somewhere?
eqUniverse :: Universe -> Universe -> Bool
eqUniverse (UVar x)  (UVar y)  = x == y
eqUniverse (UTerm x) (UTerm y) = case zipMatch x y of
    Nothing -> False
    Just z  -> all (either (const True) (uncurry eqUniverse)) z
eqUniverse _ _ = False

-- | @applicable cx u v = Just g@ means a term of type @v@ can be applied to
-- arguments of types generated by @g@ to produce a term of type @u@.  (This
-- returns a generator, not just a list of types, because we may be able to
-- freely instantiate type variables not determined by the result type.)
--
-- TODO: clean this up
--
applicable :: Context -> Universe -> UPolyType -> Maybe (Gen [Universe])
applicable cx u (U_Forall xs v0) = help [] v0
  where
    m = varsMap xs

    help :: [Universe] -> Universe -> Maybe (Gen [Universe])
    help as (UVar v)      = pure $ helpVar as v
    help as u'@(s :->: v) = tryMatch as u' `orElse` help (s:as) v
    help as u'            = tryMatch as u'

    -- Given a (reversed) accumulated list of the argument types we have
    -- committed to, and the type of the result, see if the result can be
    -- instantiated to match the target type and if so return a generator for
    -- argument types (with free variables instantiated randomly).
    tryMatch :: [Universe] -> Universe -> Maybe (Gen [Universe])
    tryMatch as u' = runUnifierM $ do
        ok <- subsumes u' u
        if ok then do arg_tys <- applyBindingsAll (reverse as)
                      fvs <- lift (getFreeVarsAll arg_tys)
                      pure $ do subs <- mapM (\a -> (,) a <$> genType cx (lookupVarKind a m)) fvs
                                pure $ substituteAll subs arg_tys
              else empty

    -- If the result type is a metavariable, we can always match the required
    -- type, but we can also create an oversaturated application by picking
    -- additional arguments to supply anyway.
    helpVar :: [Universe] -> IntVar -> Gen [Universe]
    helpVar as v = do
        tys <- listOf (genType cx U_Type)
        -- TODO: can we avoid this fromJust?
        (arg_tys, fvs) <- pure $ fromJust $ runUnifierM $ do
              lift (bindVar v (tys ->: u))
              arg_tys <- applyBindingsAll (reverse as)
              fvs <- lift (getFreeVarsAll arg_tys)
              pure (arg_tys, fvs)
        subs <- mapM (\a -> (,) a <$> genType cx (lookupVarKind a m)) fvs
        pure $ substituteAll subs (arg_tys ++ tys)

-- | Given two partial generators, produce a single partial generator that
-- chooses one of them.
orElse :: Maybe (Gen a) -> Maybe (Gen a) -> Maybe (Gen a)
orElse Nothing Nothing = Nothing
orElse mb      mb'     = Just $ oneof (catMaybes [mb,mb'])

(->:) :: [Universe] -> Universe -> Universe
(->:) = flip (foldr (:->:))



-- | Unification monad transformer stack: failure, variable bindings.
type UnifierM = ExceptT Wrong (IntBindingT UniverseF Identity)

data Wrong = Wrong

instance Semigroup Wrong where
  _ <> _ = Wrong

instance Monoid Wrong where
  mempty = Wrong

instance Fallible t v Wrong where
  occursFailure _ _ = Wrong
  mismatchFailure _ _ = Wrong

-- | Throws away any variable bindings at the end, so make sure they are applied
-- to the returned value.
runUnifierM :: UnifierM a -> Maybe a
runUnifierM m = case runIdentity (evalIntBindingT (runExceptT m)) of
    Left Wrong -> Nothing
    Right a    -> Just a

substitute :: HasCallStack => [(IntVar, Universe)] -> Universe -> Universe
substitute subs u = fromMaybe oops $ runUnifierM $ do
    mapM_ (\(a,t) -> lift (bindVar a t)) subs
    applyBindings u
  where
    oops = error $ "substitute: went wrong: " ++ show subs ++ " " ++ show u

substituteAll :: HasCallStack => [(IntVar, Universe)] -> [Universe] -> [Universe]
substituteAll subs us = fromMaybe oops $ runUnifierM $ do
    mapM_ (\(a,t) -> lift (bindVar a t)) subs
    applyBindingsAll us
  where
    oops = error $ "substituteAll: went wrong: " ++ show subs ++ " " ++ show us


--------------------------------------------------------------------------------
-- Main entry point
--------------------------------------------------------------------------------

main :: IO ()
main = do
  seed <- generate (choose (1,1000))
  putStrLn ("seed = " ++ show seed ++ "\n")
  ok <- go seed 30 True
  print ok
  putStrLn ("seed = " ++ show seed ++ "\n")

-- | Given a random seed and size, generate a module, print it out, write it to
-- disk and compile it.
go :: Int -> Int -> Bool -> IO Bool
go seed size loud = do
    let m = unGen genModule (mkQCGen seed) size
    prop_compiles loud m

-- | Test property that checks compiling a module succeeds.
prop_compiles :: Bool -> HsModule' -> IO Bool
prop_compiles loud m = do
    h <- openFile "M.hs" WriteMode
    flip finally (hClose h) $ do
      runGhc (Just libdir) $ do
        when loud $ putPpr m
        hPutPpr h m
    (ExitSuccess ==) <$> system "ghc-8.10.1 M.hs -dcore-lint +RTS -t"

test :: IO ()
test = quickCheck (forAll genModule $ ioProperty . prop_compiles False)

prop_excludes_string :: String -> HsModule' -> IO Bool
prop_excludes_string s m = do
    dyn_flags <- runGhc (Just libdir) getDynFlags
    pure $ not $ s `isInfixOf` showPpr dyn_flags m

-- | Attempt to find an example of a generated module that includes a string in
-- its pretty-printed representation.
example :: String -> IO ()
example s = quickCheck (forAll genModule $ ioProperty . prop_excludes_string s)



--------------------------------------------------------------------------------
-- Orphans
--------------------------------------------------------------------------------

-- These are terribly immoral orphans, but allow us to sample generators very
-- conveniently...

instance Show (HsDecl GhcPs) where
  show = showPpr unsafeGlobalDynFlags

instance Show (HsExpr GhcPs) where
  show = showPpr unsafeGlobalDynFlags

instance Show (HsModule GhcPs) where
  show = showPpr unsafeGlobalDynFlags

instance Show (HsType GhcPs) where
  show = showPpr unsafeGlobalDynFlags


--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

varName :: Gen OccNameStr
varName = fromString <$> ((++) <$> prefix <*> suffix)
  where
    prefix = oneof [ resize 2 lowercaseName
                   , metasyntacticVariable
                   , (\ x y -> x ++ "_" ++ y) <$> prefix <*> prefix
                   ]
    suffix = oneof [ pure ""
                   , show <$> choose (0,100::Int)
                   , elements ["'", "''", "'''"]
                   ]

tyVarName :: Gen OccNameStr
tyVarName = fromString <$> resize 1 lowercaseName

lambdaVarName :: Gen OccNameStr
lambdaVarName = fromString <$> resize 1 lowercaseName

patVarName :: Gen OccNameStr
patVarName = fromString <$> resize 2 lowercaseName


uppercaseName :: Gen String
uppercaseName = (:) <$> elements ['A'..'Z']
                    <*> listOf (elements (['A'..'Z'] ++ ['a'..'z']))

lowercaseName :: Gen String
lowercaseName = ((:) <$> elements ['a'..'z']
                      <*> listOf (elements (['A'..'Z'] ++ ['a'..'z'])))
                  `suchThat` (not . flip elem keywords)

-- | Generator of RFC 3902 compliant metasyntactic variables.
metasyntacticVariable :: Gen String
metasyntacticVariable = elements [ "foo"
                                 , "bar"
                                 , "baz"
                                 , "qux"
                                 , "quux"
                                 , "corge"
                                 , "grault"
                                 , "garply"
                                 , "waldo"
                                 , "fred"
                                 , "plugh"
                                 , "xyzzy"
                                 , "thud"
                                 ]

-- | Set of all GHC-recognised keywords. Some of these are pseudo-keywords that
-- are recognised only in specific contexts or when certain extensions are
-- enabled, but for simplicity we ban all of them.
keywords :: Set.Set String
keywords = Set.fromList
           [ "_"
           , "as"
           , "case"
           , "class"
           , "data"
           , "default"
           , "deriving"
           , "do"
           , "else"
           , "hiding"
           , "if"
           , "import"
           , "in"
           , "infix"
           , "infixl"
           , "infixr"
           , "instance"
           , "let"
           , "module"
           , "newtype"
           , "of"
           , "qualified"
           , "then"
           , "type"
           , "where"
           , "forall"
           , "mdo"
           , "family"
           , "role"
           , "pattern"
           , "static"
           , "group"
           , "by"
           , "using"
           , "foreign"
           , "export"
           , "label"
           , "dynamic"
           , "safe"
           , "interruptible"
           , "unsafe"
           , "stdcall"
           , "ccall"
           , "capi"
           , "prim"
           , "javascript"
           , "rec"
           , "proc"

           , "or" -- TODO: avoid conflicts with Prelude imports, e.g. pi
                  -- maybe use explicit Prelude import list?
           , "pi"
           , "id"
           ]

smaller :: Gen a -> Gen a
smaller = scale (`div` 2)

(@@@) :: App t => t -> [t] -> t
x @@@ [] = x
x @@@ (y:ys) = (x @@ y) @@@ ys

uniqueNames :: Ord a => Gen a -> [b] -> Gen [(a,b)]
uniqueNames gen_a = help []
  where
    help xs []     = pure (reverse xs)
    help xs (b:bs) = do
        a <- gen_a `suchThat` (isNothing . flip lookup xs)
        help ((a,b):xs) bs


-- TODO: how to implement shrinking? This will presumably require actually
-- looking at the generate HsSyn, or defining a syntax tree to generate...

-- TODO: proper support for higher kinds, including ADTs for higher kinds

-- TODO: generate let expressions, do-blocks, ...
-- TODO: generate FunBinds, where clauses

-- TODO: generate ADT decls
-- TODO: generate record fields, selection and update

-- TODO: support type class (constraints, instances)
