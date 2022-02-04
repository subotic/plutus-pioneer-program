{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module Week03.Homework2 where

import Control.Monad hiding (fmap)
import Data.Aeson (FromJSON, ToJSON)
import Data.Map as Map
import Data.Text (Text)
import Data.Void (Void)
import GHC.Generics (Generic)
import GHC.RTS.Flags (ConcFlags (ctxtSwitchTicks))
import Ledger hiding (singleton)
import Ledger.Ada as Ada
import Ledger.Constraints (TxConstraints)
import qualified Ledger.Constraints as Constraints
import qualified Ledger.Typed.Scripts as Scripts
import Playground.Contract (ToSchema, ensureKnownCurrencies, printJson, printSchemas, stage)
import Playground.TH (mkKnownCurrencies, mkSchemaDefinitions)
import Playground.Types (KnownCurrency (..))
import Plutus.Contract
import qualified PlutusTx
import PlutusTx.Prelude hiding (Semigroup (..), unless)
import Text.Printf (printf)
import Prelude (IO, Semigroup (..), Show (..), String, undefined)

{-# INLINEABLE mkValidator #-}
mkValidator :: PaymentPubKeyHash -> POSIXTime -> () -> ScriptContext -> Bool
mkValidator bf dat () ctx =
  traceIfFalse "beneficiary's signature missing" signedByBeneficiary
    && traceIfFalse "deadline not reached" deadlineReached
  where
    info :: TxInfo
    info = scriptContextTxInfo ctx

    signedByBeneficiary :: Bool
    signedByBeneficiary = txSignedBy info $ unPaymentPubKeyHash bf

    deadlineReached :: Bool
    deadlineReached = contains (from dat) $ txInfoValidRange info

data Vesting

instance Scripts.ValidatorTypes Vesting where
  type DatumType Vesting = POSIXTime
  type RedeemerType Vesting = ()

typedValidator :: PaymentPubKeyHash -> Scripts.TypedValidator Vesting
typedValidator bf =
  Scripts.mkTypedValidator @Vesting
    ($$(PlutusTx.compile [||mkValidator||]) `PlutusTx.applyCode` PlutusTx.liftCode bf)
    $$(PlutusTx.compile [||wrap||])
  where
    wrap = Scripts.wrapValidator @POSIXTime @()

validator :: PaymentPubKeyHash -> Validator
validator = Scripts.validatorScript . typedValidator

scrAddress :: PaymentPubKeyHash -> Ledger.Address
scrAddress = scriptAddress . validator

data GiveParams = GiveParams
  { gpBeneficiary :: !PaymentPubKeyHash,
    gpDeadline :: !POSIXTime,
    gpAmount :: !Integer
  }
  deriving (Generic, ToJSON, FromJSON, ToSchema)

type VestingSchema =
  Endpoint "give" GiveParams
    .\/ Endpoint "grab" ()

give :: AsContractError e => GiveParams -> Contract w s e ()
give gp = do
  let p = gpBeneficiary gp
      d = gpDeadline gp
      tx = Constraints.mustPayToTheScript d $ Ada.lovelaceValueOf $ gpAmount gp
  ledgerTx <- submitTxConstraints (typedValidator p) tx
  void $ awaitTxConfirmed $ getCardanoTxId ledgerTx
  logInfo @String $
    printf
      "made a gift of %d lovelace to %s with deadline %s"
      (gpAmount gp)
      (show $ gpBeneficiary gp)
      (show $ gpDeadline gp)

grab :: forall w s e. AsContractError e => Contract w s e ()
grab = do
  now <- currentTime
  pkh <- ownPaymentPubKeyHash
  utxos <- Map.filter (isSuitable now) <$> utxosAt (scrAddress pkh)
  if Map.null utxos
    then logInfo @String $ "no gifts available"
    else do
      let orefs = fst <$> Map.toList utxos
          lookups =
            Constraints.unspentOutputs utxos
              <> Constraints.otherScript (validator pkh)
          tx :: TxConstraints Void Void
          tx =
            mconcat [Constraints.mustSpendScriptOutput oref unitRedeemer | oref <- orefs]
              <> Constraints.mustValidateIn (from now)
      ledgerTx <- submitTxConstraintsWith @Void lookups tx
      void $ awaitTxConfirmed $ getCardanoTxId ledgerTx
      logInfo @String $ "collected gifts"
  where
    isSuitable :: POSIXTime -> ChainIndexTxOut -> Bool
    isSuitable now o = case _ciTxOutDatum o of
      Left _ -> False
      Right (Datum e) -> case PlutusTx.fromBuiltinData e of
        Nothing -> False
        Just d -> d <= now

endpoints :: Contract () VestingSchema Text ()
endpoints = awaitPromise (give' `select` grab') >> endpoints
  where
    give' = endpoint @"give" give
    grab' = endpoint @"grab" $ const grab

mkSchemaDefinitions ''VestingSchema

mkKnownCurrencies []
