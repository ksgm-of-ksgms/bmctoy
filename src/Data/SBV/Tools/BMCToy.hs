{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.BMCToy
    ( mkS
    , Symbolizable(..)
    , bmctoy
    , bmctoyWith
    ) where

import Language.Haskell.TH
import Data.Monoid (First(..), mconcat)
import Data.Maybe(fromMaybe)
import Data.SBV
import Data.SBV.Control
import Control.Monad (when)
import GHC.Generics


class Symbolizable sym con | sym -> con where
    new    :: Query sym
    toCon  :: sym -> Query con
    toSym  :: con -> sym


instance (SymVal a, SMTValue a) => Symbolizable (SBV a) a where
    new   = freshVar_
    toCon = getValue
    toSym = literal



symbolizedType :: Type -> Q Type
symbolizedType t = do
    ClassI _ dis <- reify ''Symbolizable
    sbvtype <- [t| SBV $(return t) |]
    return $ fromMaybe sbvtype $ getFirst $ mconcat $ First <$> f <$> dis
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


bmctoy :: (Symbolizable sym con, EqSymbolic sym)
    => Maybe Int
    -> Bool
    -> (sym -> SBool)
    -> (sym -> sym -> [SBool])
    -> (sym -> SBool)
    -> IO (Either String (Int, [con]))
bmctoy = bmctoyWith defaultSMTCfg


bmctoyWith :: (Symbolizable sym con, EqSymbolic sym)
        => SMTConfig
        -> Maybe Int
        -> Bool
        -> (sym -> SBool)
        -> (sym -> sym -> [SBool])
        -> (sym -> SBool)
        -> IO (Either String (Int, [con]))
bmctoyWith cfg mbLimit chatty start trans goal
  = runSMTWith cfg $ query $ do state <- new
                                constrain $ start state
                                go 0 state []
   where go i _ _
          | Just l <- mbLimit, i >= l
          = return $ Left $ "BMCToy limit of " ++ show l ++ " reached"
         go i curState sofar = do 
                                  when chatty $ io $ putStrLn $ "BMCToy: Iteration: " ++ show i
                                  push 1
                                  constrain $ goal curState
                                  cs <- checkSat
                                  case cs of
                                    Sat   -> do ms <- mapM toCon (curState : sofar)
                                                return $ Right (i, reverse ms)
                                    Unk   -> do return $ Left $ "BMCToy: Solver said unknown in iteration " ++ show i
                                    Unsat -> do pop 1
                                                nextState <- new
                                                constrain $ sAny id $ trans curState nextState
                                                go (i+1) nextState (curState : sofar)



