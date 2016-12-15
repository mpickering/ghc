{-# LANGUAGE TypeFamilies #-}

{-|


Note [CSE for Stg]
~~~~~~~~~~~~~~~~~~

This module implements a simple common subexpression elimination pass for STG. This is useful because there are expressions that we want to common up (because they are operational equivalent), but that we cannot common up in Core, because their types differ.
This was original reported as #9291.

There are two classes of code we aim for, see
note [Case 1: CSEing allocated closures] and
note [Case 2: CSEing case binders] below.


Note [Case 1: CSEing allocated closures]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

One is generated by this Haskell code:

    bar :: a -> (Either Int a, Either Bool a)
    bar x = (Right x, Right x)

which produces this Core:

    bar :: forall a. a -> (Either Int a, Either Bool a)
    bar @a x = (Right @Int @a x, Right @Bool @a x)

where the two components of the tuple are differnt terms, and cannot be
commoned up (easily). On the STG level we have

    bar [x] = let c1 = Right [x]
                  c2 = Right [x]
              in (c1,c2)

and now it is obvious that we can write

    bar [x] = let c1 = Right [x]
              in (c1,c1)

instead.


Note [Case 2: CSEing case binders]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The other case is more interesting. This Haskell Code

    foo :: Either Int a -> Either Bool a
    foo (Left 0)  = Left True
    foo (Left _)  = Left False
    foo (Right x) = Right x

produces this Core

    bar :: forall a. Either Int a -> Either Bool a
    bar @a e = case e of b { Left n -> …
                           , Right x -> Right @Bool @a x }

where we cannot CSE `Right @Bool @a x` with the case binder `b` as they have
different types. But in STG we have

    bar [e] = case e of b { Left [n] -> …
                          , Right [x] -> Right [x] }

and nothing stops us from transforming that to

    bar [e] = case e of b { Left [n] -> …
                          , Right [x] -> b}

-}
module StgCse (stgCse) where

import DataCon
import Id
import StgSyn
import Outputable
import VarEnv
import CoreSyn (AltCon(..))
import Data.List (mapAccumL)
import TrieMap
import NameEnv
import Control.Monad( (>=>) )

--------------
-- The Trie --
--------------

-- A lookup trie for data constructor appliations, i.e.
-- keys of type `(DataCon, [StgArg])`, following the patterns in TrieMap.

data StgArgMap a = SAM
    { sam_var :: DVarEnv a
    , sam_lit :: LiteralMap a
    }

instance TrieMap StgArgMap where
    type Key StgArgMap = StgArg
    emptyTM  = SAM { sam_var = emptyTM
                   , sam_lit = emptyTM }
    lookupTM (StgVarArg var) = sam_var >.> lkDFreeVar var
    lookupTM (StgLitArg lit) = sam_lit >.> lookupTM lit
    alterTM  (StgVarArg var) f m = m { sam_var = sam_var m |> xtDFreeVar var f }
    alterTM  (StgLitArg lit) f m = m { sam_lit = sam_lit m |> alterTM lit f }
    foldTM k m = foldTM k (sam_var m) . foldTM k (sam_lit m)
    mapTM f (SAM {sam_var = varm, sam_lit = litm}) =
        SAM { sam_var = mapTM f varm, sam_lit = mapTM f litm }

newtype ConAppMap a = CAM { un_cam :: DNameEnv (ListMap StgArgMap a) }

instance TrieMap ConAppMap where
    type Key ConAppMap = (DataCon, [StgArg])
    emptyTM  = CAM emptyTM
    lookupTM (dataCon, args) = un_cam >.> lkDNamed dataCon >=> lookupTM args
    alterTM  (dataCon, args) f m =
        m { un_cam = un_cam m |> xtDNamed dataCon |>> alterTM args f }
    foldTM k = un_cam >.> foldTM (foldTM k)
    mapTM f  = un_cam >.> mapTM (mapTM f) >.> CAM

-----------------
-- The CSE Env --
-----------------

{-
The main component of the environment is the trie that maps
data constructor applications to an in-scope ID that can be used instead.

The second component is an id-to-id substitiution that keeps track of what
bindings we removed, and what should be used instead.

The thirs component is an in-scope set, to rename away any binders that might
shadow an id mentioned in the other two components.
-}

type CseEnv =
    ( ConAppMap Id
    , IdEnv Id
    , InScopeSet -- Id's mentioned in the two fields above
    )

emptyEnv :: CseEnv
emptyEnv = (emptyTM, emptyVarEnv, emptyInScopeSet)

envLookup :: DataCon -> [StgArg] -> CseEnv -> Maybe Id
envLookup dataCon args (env, _, _) = lookupTM (dataCon, args) env

addEnv :: Id -> DataCon -> [StgArg] -> CseEnv -> CseEnv
-- do not bother with nullary data constructors, they are static anyways
addEnv _ _ [] env = env
addEnv bndr dataCon args (env, subst, in_scope)
    = (new_env, subst, new_in_scope)
  where
    new_env = insertTM (dataCon, args) bndr env
    new_in_scope = extendInScopeSetList in_scope $
        bndr : [ id | StgVarArg id <- args ]

forgetCse :: CseEnv -> CseEnv
forgetCse (_, subst, in_scope) = (emptyTM, subst, in_scope)
    -- See note [Free variables of an StgClosure]

addSubst :: Id -> Id -> CseEnv -> CseEnv
addSubst from to (env, subst, in_scope)
    = ( env
      , extendVarEnv subst from to
      , in_scope `extendInScopeSet` from `extendInScopeSet` to)

substArgs :: CseEnv -> [StgArg] -> [StgArg]
substArgs env = map (substArg env)

substArg :: CseEnv -> StgArg -> StgArg
substArg env (StgVarArg from) = StgVarArg (substVar env from)
substArg _   (StgLitArg lit)  = StgLitArg lit

substVars :: CseEnv -> [Id] -> [Id]
substVars env = map (substVar env)

substVar :: CseEnv -> Id -> Id
substVar (_, subst, _) from
    | Just to <- lookupVarEnv subst from = to
    | otherwise                          = from

-- Functions to enter binders

-- This is cargo-culted from CoreSubst, but much simpler because we do not have
-- type substitutions, nor is there something relevant in IdInfo at this stage
-- that needs substitutions (is that really true?)

substBndr :: CseEnv -> Id -> (CseEnv, Id)
substBndr env@(_, _, in_scope) old_id
  = (new_env, new_id)
  where
    new_id = uniqAway in_scope old_id
    no_change = new_id == old_id
    new_env | no_change = env
            | otherwise = addSubst old_id new_id env

substBndrs :: CseEnv -> [Var] -> (CseEnv, [Var])
substBndrs env bndrs = mapAccumL substBndr env bndrs

substPairs :: CseEnv -> [(Var, a)] -> (CseEnv, [(Var, a)])
substPairs env bndrs = mapAccumL go env bndrs
  where go env (id, x) = let (env', id') = substBndr env id
                         in (env', (id', x))

-- Main entry point

stgCse :: [StgBinding] -> [StgBinding]
stgCse binds = map stgCseTopLvl binds

-- Top level bindings.
--
-- We do not CSE these, as closure applications here are
-- static anyways. Also, they might be exported.

stgCseTopLvl :: StgBinding -> StgBinding
stgCseTopLvl (StgNonRec bndr rhs)
    = StgNonRec bndr (stgCseTopLvlRhs rhs)
stgCseTopLvl (StgRec eqs)
    = StgRec [ (bndr, stgCseTopLvlRhs rhs) | (bndr, rhs) <- eqs ]

stgCseTopLvlRhs :: StgRhs -> StgRhs
stgCseTopLvlRhs (StgRhsClosure ccs info occs upd args body)
    = let body' = stgCseExpr emptyEnv body
      in  StgRhsClosure ccs info occs upd args body'
stgCseTopLvlRhs (StgRhsCon ccs dataCon args)
    = StgRhsCon ccs dataCon args

------------------------------
-- The actual AST traversal --
------------------------------

-- Trivial cases
stgCseExpr :: CseEnv -> StgExpr -> StgExpr
stgCseExpr env (StgApp fun args)
    = StgApp fun' args'
  where fun' = substVar env fun
        args' = substArgs env args
stgCseExpr _ (StgLit lit)
    = StgLit lit
stgCseExpr env (StgOpApp op args tys)
    = StgOpApp op args' tys
  where args' = substArgs env args
stgCseExpr _ (StgLam _ _)
    = pprPanic "stgCseExp" (text "StgLam")
stgCseExpr env (StgTick tick body)
    = let body' = stgCseExpr env body
      in StgTick tick body'
stgCseExpr env (StgCase scrut bndr ty alts)
    = let scrut' = stgCseExpr env scrut
          (env', bndr') = substBndr env bndr
          alts' = map (stgCseAlt env' bndr') alts
      in StgCase scrut' bndr' ty alts'

-- A constructor application.
-- To be removed by a variable use when found in the CSE environment
stgCseExpr env (StgConApp dataCon args tys)
    | Just bndr' <- envLookup dataCon args' env
    = StgApp bndr' []
    | otherwise
    = StgConApp dataCon args' tys
  where args' = substArgs env args


-- Let bindings
-- The binding might be removed due to CSE (we do not want trivial bindings on
-- the STG level), so use the smart constructor `mkStgLet` to remove the binding
-- if empty.
stgCseExpr env (StgLet binds body)
    = let (binds', env') = stgCseBind env binds
          body' = stgCseExpr env' body
      in mkStgLet StgLet binds' body'
stgCseExpr env (StgLetNoEscape binds body)
    = let (binds', env') = stgCseBind env binds
          body' = stgCseExpr env' body
      in mkStgLet StgLetNoEscape binds' body'

-- Case alternatives
-- Extend the CSE environment
stgCseAlt :: CseEnv -> Id -> StgAlt -> StgAlt
stgCseAlt env case_bndr (DataAlt dataCon, args, rhs)
    = let (env1, args') = substBndrs env args
          env2 = addEnv case_bndr dataCon (map StgVarArg args') env1
            -- see note [Case 2: CSEing case binders]
          rhs' = stgCseExpr env2 rhs
      in (DataAlt dataCon, args', rhs')
stgCseAlt env _ (altCon, args, rhs)
    = let (env1, args') = substBndrs env args
          rhs' = stgCseExpr env1 rhs
      in (altCon, args', rhs')

-- Bindings
stgCseBind :: CseEnv -> StgBinding -> (Maybe StgBinding, CseEnv)
stgCseBind env (StgNonRec b e)
    = let (env1, b1) = substBndr env b
      in case stgCseRhs env1 b1 e of
        (Nothing,      env2) -> (Nothing,                env2)
        (Just (b2,e'), env2) -> (Just (StgNonRec b2 e'), env2)
stgCseBind env (StgRec pairs)
    = let (env1, pairs1) = substPairs env pairs
      in case stgCsePairs env1 pairs1 of
        ([],     env2) -> (Nothing, env2)
        (pairs2, env2) -> (Just (StgRec pairs2), env2)

stgCsePairs :: CseEnv -> [(Id, StgRhs)] -> ([(Id, StgRhs)], CseEnv)
stgCsePairs env [] = ([], env)
stgCsePairs env0 ((b,e):pairs)
  = let (pairMB, env1) = stgCseRhs env0 b e
        (pairs', env2) = stgCsePairs env1 pairs
    in (pairMB `mbCons` pairs', env2)
  where
    mbCons = maybe id (:)

-- The RHS of a binding.
-- If it is an constructor application, either short-cut it or extend the environment
stgCseRhs :: CseEnv -> Id -> StgRhs -> (Maybe (Id, StgRhs), CseEnv)
stgCseRhs env bndr (StgRhsCon ccs dataCon args)
    | Just bndr' <- envLookup dataCon args' env
    = (Nothing, addSubst bndr bndr' env)
    | otherwise
    = let env' = addEnv bndr dataCon args' env
            -- see note [Case 1: CSEing allocated closures]
      in (Just (bndr, StgRhsCon ccs dataCon args'), env')
  where args' = substArgs env args
stgCseRhs env bndr (StgRhsClosure ccs info occs upd args body)
    = let (env1, args') = substBndrs env args
          env2 = forgetCse env1 -- See note [Free variables of an StgClosure]
          body' = stgCseExpr env2 body
      in (Just (bndr, StgRhsClosure ccs info occs' upd args' body'), env)
  where occs' = substVars env occs

-- Utilities

-- | This function short-cuts let-bindings that are now obsolete
mkStgLet :: (t2 -> t1 -> t1) -> Maybe t2 -> t1 -> t1
mkStgLet _      Nothing      body = body
mkStgLet stgLet (Just binds) body = stgLet binds body


{-
Note [Free variables of an StgClosure]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

StgClosures (function and thunks) have an explicit list of free variables:

foo [x] =
    let not_a_free_var = Left [x]
    let a_free_var = Right [x]
    let closure = \[a_free_var] -> \[y] -> bar y (Left [x]) a_free_var
    in closure

If we were to CSE `Left [x]` in the body of `closure` with `not_a_free_var`,
then the list of free variables would be wrong, so for now, we do not CSE
across such a closure, simply because I (Joachim) was not sure about possible
knock-on effects. If deemed safe and worth the slight code complication of
re-calculating this list during or after this pass, this can surely be done.
-}
