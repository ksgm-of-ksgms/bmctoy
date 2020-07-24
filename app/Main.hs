{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE TypeOperators #-}
--{-# OPTIONS_GHC -Wall -Werror #-}

import Data.SBV
import Data.SBV.Tools.BMCToy
import Data.SBV.Maybe
--import Control.Lens
import GHC.Generics
import Data.Generics.Product


data Event = Coin | Fill Integer | Lucky deriving (Generic, Show)


data Msg = Soldout


mkSymbolicEnumeration ''Msg


data Model  = Model  {  coin ::  Integer,  juice :: Integer, msg ::  Maybe Msg} deriving (Generic, Show)

maxCoin :: (Num a) => a
maxCoin = 5

maxJuice :: (Num a) => a
maxJuice = 5

-- generation code --------

type PModel = (Integer, Integer, Maybe Msg)

type SModel = SBV PModel

type PEvent = () |+| Integer |+| ()

type SEvent = SBV PEvent

instance PrimitiveIso Event PEvent where
    toPrim   Coin           = Left ()
    toPrim   (Fill n)       = Right (Left n)
    toPrim   Lucky          = Right (Right ())
    fromPrim  (Left ())     = Coin
    fromPrim  (Right (Left n))     = Fill n
    fromPrim  (Right (Right ()))   = Lucky

instance PrimitiveIso Model PModel where
    toPrim   (Model x y z) = (x, y, z)
    fromPrim (x, y, z) = Model x y z


_scoin = _s1
_sjuice = _s2
_smsg = _s3

_sCoin = _sLeft
_sFill = _sRight .-> _sLeft
_sLucky = _sRight .-> _sRight

-----------------------------------

trans :: SEvent -> SModel -> SModel -> [SBool]
trans e s s' = [ e .== _sCoin .# literal ()
                    .&& s' .^. _scoin .<= maxCoin
                    .&& s' .^. _scoin .== s .^. _scoin + 1
                    .&& s' .^. _sjuice .== s .^. _sjuice - 1
                    .&& s' .^. _sjuice .>= 0
                    .&& msgInvariant s'
               , e `sis` _sFill
                    .&& e .^?! _sFill .> 0
                    .&& s' .^. _scoin .== 0
                    .&& s' .^. _sjuice .== s .^. _sjuice + e .^?! _sFill
                    .&& s' .^. _sjuice .<= maxJuice
                    .&& s' .^. _sjuice .>= 0
                    .&& s' .^. _smsg .== sNothing
               , e .== _sLucky .# literal ()
                    .&& s' .^. _scoin .<= maxCoin
                    .&& s' .^. _scoin .== s .^. _scoin + 1
                    .&& s' .^. _sjuice .== s .^. _sjuice - 2
                    .&& s' .^. _sjuice .>= 0
                    .&& msgInvariant s'
               ]

coinInvariant :: SModel -> SBool
coinInvariant s =     s .^. _scoin .>= 0
                  .&& s .^. _scoin .<= maxCoin
                  .&& s .^. _sjuice .>= 0
                  .&& s .^. _sjuice .<= maxJuice

msgInvariant :: SModel -> SBool
msgInvariant s = ite (s .^. _sjuice .== 0) (s .^. _smsg .== literal (Just Soldout)) (s .^. _smsg .== sNothing)

start :: SModel -> SBool
start smodel = smodel .== toPrim' (Model 0 maxJuice Nothing)

goal :: SModel -> SBool
goal smodel =  sNot (coinInvariant smodel .&& msgInvariant smodel)


main :: IO ()
main = do
        result <- bmctoy (Just 15) start trans goal
        case result of
            BTRReached evs sts  -> do
                                      sequence_ $ print <$> [fromPrim @Event s| s <- evs]
                                      sequence_ $ print <$> [fromPrim @Model s| s <- sts]
            _ -> print result


