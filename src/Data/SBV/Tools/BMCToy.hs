{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-#LANGUAGE GADTs #-}

--{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.BMCToy
    ( mkS
    , Symbolizable(..)
    , bmctoy
    , _sLeft
    , _sRight
    , (.#)
    , sis
    , HasField1(..)
    , HasField2(..)
    , HasField3(..)
    , HasField4(..)
    , PrimitiveIso (..)
    , (.->)
    , (.^.)
    , (.^?)
    , (.^?!)
    , (..~)
    , (.%~)
    , type (|+|)
    , SOptic(..)
    , BMCToyResult(..)
    ) where

import Language.Haskell.TH
import Data.Monoid (First(..), mconcat)
import Data.Maybe as M
import Data.SBV
import Data.SBV.Control
import Control.Monad (when)
import GHC.Generics
import Data.Type.Bool (If, type (&&), Not)
import Data.Proxy
import Data.SBV.Maybe  as SM
import Data.SBV.Either as SE
import Data.SBV.Tuple  as ST
import Control.Lens as L


type a |+| b = Either a b
infixr 5 |+|

(.>>=) :: (SymVal a, SymVal b) => SBV (Maybe a) -> (SBV a -> SBV (Maybe b)) -> SBV (Maybe b)
a .>>= b = ite (SM.isJust a) (b $ SM.fromJust a) sNothing

(.>=>) :: (SymVal a, SymVal b, SymVal c) => (SBV a -> SBV (Maybe b)) -> (SBV b -> SBV (Maybe c)) -> SBV a -> SBV (Maybe c)
a .>=> b = \x -> a x .>>= b

data SOptic (bc::Bool) (bg::Bool) s a where
    STrav  :: (SBV s -> SBV a -> SBV s) -> (SBV s -> SBV (Maybe a)) -> SOptic 'False 'False s a
    SLens  :: (SBV s -> SBV a -> SBV s) -> (SBV s -> SBV a        ) -> SOptic 'False 'True s a
    SPrism :: (SBV a -> SBV s         ) -> (SBV s -> SBV (Maybe a)) -> SOptic 'True  'False s a

(.^.) :: SBV s -> SOptic b 'True s a -> SBV a
s .^. (SLens _ g) = g s

infixl 8 .^.

(.^?) :: SBV s -> SOptic b 'False s a -> SBV (Maybe a)
s .^? (SPrism _ g) = g s
s .^? (STrav  _ g) = g s

infixl 8 .^?

(.^?!) :: (SymVal a) => SBV s -> SOptic b 'False s a -> SBV a
s .^?! l = SM.fromJust $ s .^? l

infixl 8 .^?!

sis :: (SymVal a) => SBV s -> SOptic b 'False s a -> SBool
sis s l = SM.isJust $ s .^? l

(..~) :: SOptic b0 b1 s a -> SBV a -> SBV s -> SBV s
(STrav u _) ..~ a = (`u` a)
(SLens u _) ..~ a = (`u` a)
(SPrism u _) ..~ a = \_ -> u a

infixr 4 ..~

(.%~) :: (SymVal s, SymVal a) => SOptic b0 b1 s a -> (SBV a -> SBV a) -> SBV s -> SBV s
(STrav u g) .%~ f = \s -> ite (SM.isJust $ g s) (u s $ f $ SM.fromJust $ g s) s
(SLens u g) .%~ f = \s -> u s $ f $ g s
(SPrism u g) .%~ f = \s -> ite (SM.isJust $ g s) (u $ f $ SM.fromJust $ g s) s

infixr 4 .%~

sre :: SOptic 'True b s a -> SBV a -> SBV s
sre (SPrism f _) = f

(.#) :: SOptic 'True b s a -> SBV a -> SBV s
(.#) = sre
infixr 8 .#

(.->) :: (SymVal a, SymVal b, SymVal c) => SOptic b0 t0 a b -> SOptic b1 t1 b c -> SOptic (b0 && b1) (t0 && t1) a c
SLens u0 g0 .-> SLens u1 g1 = SLens (\s c -> u0 s (u1 (g0 s) c)) (g1 . g0)
SLens u0 g0 .-> SPrism u1 g1 = STrav  (\s a -> u0 s (u1 a)) (g1 . g0)
SLens u0 g0 .-> STrav  u1 g1 = STrav  u2 g2
    where
    g2 s = g1 $ g0 s
    u2 s a = u0 s (u1 (g0 s) a)
SPrism u0 g0 .-> SLens u1 g1 = STrav  u2 g2
    where
    u2 s c = ite (SM.isJust b) (u0 $ u1 (SM.fromJust b) c) s
        where
        b = g0 s
    g2 s = ite (SM.isJust b) (sJust $ g1 $ SM.fromJust b) sNothing
        where
        b = g0 s
SPrism u0 g0 .-> SPrism u1 g1 = SPrism u2 g2
    where
    u2 = u0 . u1
    g2 = g0 .>=> g1
SPrism u0 g0 .-> STrav  u1 g1 = STrav  u2 g2
    where
    u2 s c = ite (SM.isJust b) (u0 $ u1 (SM.fromJust b) c) s
        where
        b = g0 s
    g2 = g0 .>=> g1
STrav  u0 g0 .-> SLens u1 g1 = STrav  u2 g2
    where
    u2 s c = ite (SM.isJust b) (u0 s (u1 (SM.fromJust b) c)) s
        where
        b = g0 s
    g2 s = ite (SM.isJust b) (sJust $ g1 $ SM.fromJust b) sNothing
        where
        b = g0 s
STrav  u0 g0 .-> SPrism u1 g1 = STrav  u2 g2
    where
    u2 s a = u0 s $ u1 a
    g2 = g0 .>=> g1
STrav  u0 g0 .-> STrav  u1 g1 = STrav  u2 g2
    where
    u2 s c = ite (SM.isJust b) (u0 s (u1 (SM.fromJust b) c)) s
        where
        b = g0 s
    g2 = g0 .>=> g1


infixr 9 .->

_sLeft :: (SymVal a, SymVal b) => SOptic 'True 'False (Either a b) a
_sLeft = SPrism SE.sLeft (SE.either SM.sJust $ const SM.sNothing)


_sRight :: (SymVal a, SymVal b) => SOptic 'True 'False (Either a b) b
_sRight = SPrism SE.sRight (SE.either (const SM.sNothing) SM.sJust)

--_sJust
--_sNothing


class (SymVal elm) => HasField1 tup elm | tup -> elm where
  _s1 :: SOptic 'False 'True tup elm

class (SymVal elm) => HasField2 tup elm | tup -> elm where
  _s2 :: SOptic 'False 'True tup elm

class (SymVal elm) => HasField3 tup elm | tup -> elm where
  _s3 :: SOptic 'False 'True tup elm

class (SymVal elm) => HasField4 tup elm | tup -> elm where
  _s4 :: SOptic 'False 'True tup elm

tupU l s a = tuple $ untuple s & l .~ a

instance (SymVal a, SymVal b) => HasField1 (a, b) a where
    _s1 = SLens (tupU L._1) ST._1

instance (SymVal a, SymVal b) => HasField2 (a, b) b where
    _s2 = SLens (tupU L._2) ST._2

instance (SymVal a, SymVal b, SymVal c) => HasField1 (a, b, c) a where
    _s1 = SLens (tupU L._1) ST._1

instance (SymVal a, SymVal b, SymVal c) => HasField2 (a, b, c) b where
    _s2 = SLens (tupU L._2) ST._2

instance (SymVal a, SymVal b, SymVal c) => HasField3 (a, b, c) c where
    _s3 = SLens (tupU L._3) ST._3

instance (SymVal a, SymVal b, SymVal c, SymVal d) => HasField1 (a, b, c, d) a where
    _s1 = SLens (tupU L._1) ST._1

instance (SymVal a, SymVal b, SymVal c, SymVal d) => HasField2 (a, b, c, d) b where
    _s2 = SLens (tupU L._2) ST._2

instance (SymVal a, SymVal b, SymVal c, SymVal d) => HasField3 (a, b, c, d) c where
    _s3 = SLens (tupU L._3) ST._3

instance (SymVal a, SymVal b, SymVal c, SymVal d) => HasField4 (a, b, c, d) d where
    _s4 = SLens (tupU L._4) ST._4



class PrimitiveIso a p | a -> p where
    toPrim   :: a -> p
    fromPrim :: p -> a
    toPrim'  :: (SymVal p) => a -> SBV p
    toPrim' = literal . toPrim



class Symbolizable sym con | sym -> con where
    new    :: Query sym
    toCon  :: sym -> Query con
    toSym  :: con -> sym


instance (SymVal a) => Symbolizable (SBV a) a where
    new   = freshVar_
    toCon = getValue
    toSym = literal


symbolizedType :: Type -> Q Type
symbolizedType t = do
    ClassI _ dis <- reify ''Symbolizable
    sbvtype <- [t| SBV $(return t) |]
    return $ M.fromMaybe sbvtype $ getFirst $ mconcat $ First <$> f <$> dis
    where
    f :: Dec -> Maybe Type
    f (InstanceD _ _ (AppT (AppT _ sym) con) _) = if con == t then Just sym else Nothing
    f _ = Nothing


convName :: Name -> Name
convName nm = mkName $ "S" ++ nameBase nm


declSType :: Name -> Q [Dec]
declSType nm = do
            TyConI (DataD ctx tcstr tbr kd [RecC dcstr flds] _) <- reify nm -- why is dervs []??
            flds' <- traverse (\(n, b, t) -> (n, b, ) <$> symbolizedType t) flds
            genericclass <- [t|Generic|]
            let dervs = [DerivClause Nothing [genericclass]]
            let declS = DataD ctx (convName tcstr) tbr kd [RecC (convName dcstr) flds'] dervs
            return [declS]


declEqSymbolicInstance :: Name -> Q [Dec]
declEqSymbolicInstance nm = do
            let nm' = convName nm
            TyConI (DataD _ _ _ _ [RecC _ flds] _) <- reify nm
            let fldnames = [n | (n, _, _) <- flds]
            let fps1 = mkFieldPat "1" fldnames
            let fps2 = mkFieldPat "2" fldnames
            let eqexps = fps2eqexp <$> zip fps1 fps2
            let insd = InstanceD Nothing [] (AppT (ConT ''EqSymbolic) (ConT nm')) [
                        FunD eqsym [ Clause [RecP nm' fps1 ,RecP nm' fps2 ] (NormalB $ intersperseAnd eqexps) [] ]
                        ]
            return [insd]
            where
            mkFieldPat :: String -> [Name] -> [FieldPat]
            mkFieldPat postfix = fmap f
                where
                f :: Name -> FieldPat
                f name = (name, VarP $ mkName $ nameBase name ++ postfix)

            fps2eqexp :: (FieldPat, FieldPat) -> Exp
            fps2eqexp ((_, VarP v1), (_,VarP v2)) = InfixE (Just (VarE v1)) (VarE eqsym) (Just (VarE v2))
            fps2eqexp _ = error "invalid match"

            intersperseAnd :: [Exp] -> Exp
            intersperseAnd []  = error "invalid match"
            intersperseAnd [e] = e
            intersperseAnd (e:es) = InfixE (Just e) 
                                            (VarE andsym)
                                            (Just $ intersperseAnd es)

            eqsym = mkName ".=="
            andsym = mkName ".&&"


--data Model  = Model  {  x ::  Integer,  y ::  Integer} deriving (Show)
--data SModel  = SModel  {  x ::  SBV Integer,  y ::  SBV Integer} deriving (Show)



declSymbolizableInstance :: Name -> Q [Dec]
declSymbolizableInstance nm = do
            TyConI (DataD _ _ _ _ [RecC dcstr flds] _) <- reify nm
            let numfield = length flds
            conVars <- traverse newName ["arg" ++ show i| i <- [1 .. numfield]]
            symVars <- traverse newName ["arg" ++ show i| i <- [1 .. numfield]]
            let d = InstanceD Nothing [] (AppT (AppT (ConT ''Symbolizable) (ConT nm')) (ConT nm))
                    [ ValD (VarP 'new) (NormalB $ newBody numfield) []
                    , FunD 'toCon [Clause [ConP nm' (VarP <$> conVars)] (NormalB $ conBody dcstr $ reverse conVars) []]
                    , FunD 'toSym [Clause [ConP dcstr  (VarP <$> symVars)] (NormalB $ symBody $ reverse symVars) []]
                    ]
            return [d]
            where
            nm' = convName nm
            newBody n | n == 1 = InfixE (Just (ConE nm')) (VarE '(<$>)) (Just (VarE 'create))
                      | n > 1  = InfixE (Just (newBody (n-1))) (VarE '(<*>)) (Just (VarE 'create))
                      | otherwise = error "invalid match"

            conBody _ []      = error "invalid match"
            conBody s [v]    = InfixE (Just (ConE s)) (VarE '(<$>)) (Just (AppE (VarE 'toCon) (VarE v)))
            conBody s (v:vs) = InfixE (Just (conBody s vs)) (VarE '(<*>)) (Just (AppE (VarE 'toCon) (VarE v)))

            symBody []     = error "invalid match"
            symBody [v]    = AppE (ConE nm') (AppE (VarE 'toSym) (VarE v))
            symBody (v:vs) = AppE (symBody vs) (AppE (VarE 'toSym) (VarE v))


mkS :: Name -> Q [Dec]
mkS nm = do
            dt  <- declSType nm
            dei <- declEqSymbolicInstance nm
            dqi <- declSymbolizableInstance nm
            return $ dt ++ dei ++ dqi


data BMCToyResult cev cst = BTRLimitReached Int | BTRReached [cev] [cst] | BTRDeadlock [cev] [cst] | BTRUnknown Int deriving Show

bmctoy :: (Symbolizable sev cev, EqSymbolic sev, Symbolizable sst cst, EqSymbolic sst)
        => Maybe Int
        -> (sst -> SBool)
        -> (sev -> sst -> sst -> [SBool])
        -> (sst -> SBool)
        -> IO (BMCToyResult cev cst)
bmctoy mbLimit start trans goal
  = runSMTWith defaultSMTCfg $ query $ do state <- new
                                          constrain $ start state
                                          go 0 state [] []
   where go i _ _ _ | Just l <- mbLimit, i >= l = return $ BTRLimitReached i
         go i curState sts evs = do
                                  io $ putStrLn $ "BMCToy: Iteration: " ++ show i
                                  push 1
                                  constrain $ goal curState
                                  cs <- checkSat
                                  case cs of
                                    Sat   -> do csts <- mapM toCon (curState : sts)
                                                cevs <- mapM toCon evs
                                                return $ BTRReached (reverse cevs) (reverse csts)
                                    Unk   -> return $ BTRUnknown i
                                    Unsat -> do pop 1
                                                nextState <- new
                                                ev    <- new
                                                push 1
                                                cd <- checkDeadLock ev curState nextState
                                                if cd
                                                    then do
                                                        csts <- mapM toCon sts
                                                        cevs <- mapM toCon evs
                                                        return $ BTRDeadlock (reverse cevs) (reverse csts)
                                                    else do
                                                            pop 1
                                                            constrain $ sAny id $ trans ev curState nextState
                                                            go (i+1) nextState (curState : sts) (ev : evs)
         checkDeadLock ev s s' = do
                                    return False
                                    --constrain $ sNot $ sAny id $ trans ev s s'
                                    --cs <- checkSat
                                    --case cs of
                                    --  Sat   -> return True
                                    --  Unk   -> return False
                                    --  Unsat -> return False



