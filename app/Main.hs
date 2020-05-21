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
{-# OPTIONS_GHC -Wall -Werror #-}

import Data.SBV
import Data.SBV.Tools.BMCToy
import Control.Lens
import GHC.Generics
import Data.Generics.Product

data State = StA | StB

mkSymbolicEnumeration ''State

data Model  = Model  {  x ::  Integer,  y ::  State} deriving (Generic, Show)

mkS ''Model


problem :: IO (Either String (Int, [Model]))
problem = bmctoy (Just 5) True start trans goal
    where
    trans :: SModel -> SModel -> [SBool]
    trans s s' = [ s' ^. field @"x" .== s ^. field @"x" + 2 .&& s' ^. field @"y" .==  toSym StB
                 , s' .== (s &~ do { field @"y" .= toSym StA} )
                 ]

    start :: SModel -> SBool
    start smodel = smodel .== toSym (Model 1 StA)

    goal :: SModel -> SBool
    goal SModel{ x,  y} =  x .== 5 .&&  y .== toSym StA


main :: IO ()
main = print =<< problem
