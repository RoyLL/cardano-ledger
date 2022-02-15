{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Cardano.Ledger.Babbage.Rules.Utxo where

import Data.Coerce (coerce)
import qualified Data.Compact.SplitMap as SplitMap
import Data.Either (isRight)
import Data.Foldable (foldl', sequenceA_)
import Data.List.NonEmpty (NonEmpty)
import Data.Ratio ((%))
import Data.Sequence.Strict (StrictSeq)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import GHC.Records
import NoThunks.Class (NoThunks)
import Numeric.Natural (Natural)
import Validation

import Cardano.Ledger.Alonzo.Rules.Utxos (UtxosPredicateFailure (..))
import Cardano.Ledger.Alonzo.Rules.Utxow (AlonzoPredFail)
import Cardano.Ledger.Alonzo.Tx (minfee)
import Cardano.Ledger.Alonzo.TxWitness (TxWitness (..), nullRedeemers)
import Cardano.Ledger.Babbage.Collateral (collBalance, minCollateral,feesOK)
-- import Cardano.Ledger.Babbage.Rules.Utxos (BabbageUTXOS)
import Cardano.Ledger.Babbage.Tx (ValidatedTx (..), wits, txouts)
import Cardano.Ledger.Babbage.TxBody
  ( TxBody (..),
    TxOut,
    collateral',
    collateralReturn',
    totalCollateral',
    txfee',
  )
import Cardano.Ledger.Alonzo.Rules.Utxo
  ( validateCollateral,
    validateScriptsNotPaidUTxO,
    validateInsufficientCollateral,
    validateCollateralContainsNonADA,
    validateOutsideForecast,
    validateOutputTooSmallUTxO,
    validateOutputTooBigUTxO,
    validateWrongNetworkInTxBody,
    validateExUnitsTooBigUTxO,
    validateTooManyCollateralInputs,
    -- AlonzoUtxoNeeds,
    -- FeeNeeds,
    -- UtxoDelta (UtxoDelta),
    UtxoEvent (..),
    UtxoPredicateFailure (..),
    -- genericAlonzoUtxo,
    vKeyLocked,
    AlonzoUTXO,
    fromShelleyFailure,
    fromShelleyMAFailure,
  )
import qualified Cardano.Ledger.ShelleyMA.Rules.Utxo as ShelleyMA
 ( validateOutsideValidityIntervalUTxO,
   validateValueNotConservedUTxO,
   validateTriesToForgeADA,
 )
 
import qualified Cardano.Ledger.Core as Core
import Control.State.Transition.Extended
  ( Embed (..),
    Rule,
    RuleType (Transition),
    STS (..),
    TRC(..),
    TransitionRule(..),
    (?!),
    liftSTS,
    trans,
    judgmentContext,
  )
import Cardano.Ledger.Address
  ( Addr (..),
    RewardAcnt,
    getNetwork,
    getRwdNetwork,
  )
import Cardano.Ledger.Alonzo.Data (DataHash, dataHashSize)
import Cardano.Ledger.Alonzo.Rules.Utxos (UTXOS, UtxosPredicateFailure)
import Cardano.Ledger.Alonzo.Scripts (ExUnits (..), Prices, pointWiseExUnits)
import Cardano.Ledger.Alonzo.Tx (ValidatedTx (..), minfee, totExUnits)
import qualified Cardano.Ledger.Alonzo.Tx as Alonzo (ValidatedTx)
import qualified Cardano.Ledger.Alonzo.TxSeq as Alonzo (TxSeq)
import Cardano.Ledger.Alonzo.TxWitness (TxWitness (txrdmrs'), nullRedeemers)
import Cardano.Ledger.BaseTypes
  ( Network,
    ShelleyBase,
    StrictMaybe (..),
    epochInfoWithErr,
    networkId,
    systemStart,
  )
import Cardano.Ledger.Coin
import Cardano.Ledger.CompactAddress
  ( CompactAddr,
    isBootstrapCompactAddr,
    isPayCredScriptCompactAddr,
  )

import qualified Cardano.Ledger.Shelley.LedgerState as Shelley
import qualified Cardano.Ledger.Shelley.Rules.Utxo as Shelley
import Cardano.Ledger.Era (Era (..), ValidateScript (..))
import qualified Cardano.Ledger.Era as Era
import Cardano.Ledger.Shelley.Tx (TxIn)
import Cardano.Ledger.Shelley.TxBody (DCert, Wdrl, unWdrl)
import Cardano.Binary (FromCBOR (..), ToCBOR (..), serialize)
import Cardano.Ledger.Shelley.Constraints (UsesPParams)
import Cardano.Ledger.ShelleyMA.Timelocks (ValidityInterval (..), inInterval)
import Cardano.Ledger.Rules.ValidationMode
  ( mapMaybeValidation,
    runValidation,
    runValidationStatic,
    runValidationStaticTransMaybe,
    runValidationTransMaybe,
  )
import Control.Monad.Trans.Reader (asks)  
  
-- ========================================================

-- | Predicate failure for the Babbage Era
data BabbageUtxoPred era
  = FromAlonzoUtxoFail (UtxoPredicateFailure era)
  | FromAlonzoUtxowFail (AlonzoPredFail era)
  | UnequalCollateralReturn Coin Coin

deriving instance
  ( Era era,
    Show (UtxoPredicateFailure era),
    Show (PredicateFailure (Core.EraRule "UTXO" era)),
    Show (Core.Script era)
  ) =>
  Show (BabbageUtxoPred era)

deriving instance
  ( Era era,
    Eq (UtxoPredicateFailure era),
    Eq (PredicateFailure (Core.EraRule "UTXO" era)),
    Eq (Core.Script era)
  ) =>
  Eq (BabbageUtxoPred era)

-- TODO FIXME  add CBOR instances
-- | The UTxO transition rule for the Alonzo eras.
utxoTransition ::
  forall era.
  ( Era era,
    ValidateScript era,
    -- instructions for calling UTXOS from AlonzoUTXO
    Embed (Core.EraRule "UTXOS" era) (AlonzoUTXO era),
    Environment (Core.EraRule "UTXOS" era) ~ Shelley.UtxoEnv era,
    State (Core.EraRule "UTXOS" era) ~ Shelley.UTxOState era,
    Signal (Core.EraRule "UTXOS" era) ~ Core.Tx era,
    -- We leave Core.PParams abstract
    UsesPParams era,
    Core.ChainData (Core.Value era),
    Core.ChainData (Core.TxOut era),
    Core.ChainData (Core.TxBody era),
    HasField "_minfeeA" (Core.PParams era) Natural,
    HasField "_minfeeB" (Core.PParams era) Natural,
    HasField "_keyDeposit" (Core.PParams era) Coin,
    HasField "_poolDeposit" (Core.PParams era) Coin,
    HasField "_maxTxSize" (Core.PParams era) Natural,
    HasField "_prices" (Core.PParams era) Prices,
    HasField "_maxTxExUnits" (Core.PParams era) ExUnits,
    HasField "_coinsPerUTxOWord" (Core.PParams era) Coin,
    HasField "_maxValSize" (Core.PParams era) Natural,
    HasField "_collateralPercentage" (Core.PParams era) Natural,
    HasField "_maxCollateralInputs" (Core.PParams era) Natural,
    Core.Tx era ~ Alonzo.ValidatedTx era,
    Core.Witnesses era ~ TxWitness era,
    Era.TxSeq era ~ Alonzo.TxSeq era,
    HasField "vldt" (Core.TxBody era) ValidityInterval,
    HasField "inputs" (Core.TxBody era) (Set (TxIn (Crypto era))),
    HasField "collateral" (Core.TxBody era) (Set (TxIn (Crypto era))),
    HasField "mint" (Core.TxBody era) (Core.Value era),
    HasField "wdrls" (Core.TxBody era) (Wdrl (Crypto era)),
    HasField "certs" (Core.TxBody era) (StrictSeq (DCert (Crypto era))),
    HasField "datahash" (Core.TxOut era) (StrictMaybe (DataHash (Crypto era))),
    ToCBOR (Core.Value era),
    HasField "txnetworkid" (Core.TxBody era) (StrictMaybe Network)
  ) =>
  TransitionRule (AlonzoUTXO era)
utxoTransition = do
  TRC (Shelley.UtxoEnv slot pp stakepools _genDelegs, u, tx) <- judgmentContext
  let Shelley.UTxOState utxo _deposits _fees _ppup _ = u

  {-   txb := txbody tx   -}
  let txb = body tx
      inputsAndCollateral =
        Set.union
          (getField @"inputs" txb)
          (getField @"collateral" txb)

  {- ininterval slot (txvld txb) -}
  runValidationTransMaybe fromShelleyMAFailure $
    ShelleyMA.validateOutsideValidityIntervalUTxO slot txb

  sysSt <- liftSTS $ asks systemStart
  ei <- liftSTS $ asks epochInfoWithErr

  {- epochInfoSlotToUTCTime epochInfo systemTime i_f ≠ ◇ -}
  runValidation $ validateOutsideForecast ei sysSt tx

  {-   txins txb ≠ ∅   -}
  runValidationStaticTransMaybe fromShelleyFailure $ Shelley.validateInputSetEmptyUTxO txb

  {-   feesOK pp tx utxo   -}
  runValidation $ whoops (feesOK pp tx utxo) -- Generalizes the fee to small from earlier Era's

  {- inputsAndCollateral = txins txb ∪ collateral txb -}
  {- (txins txb) ∪ (collateral txb) ⊆ dom utxo   -}
  runValidationTransMaybe fromShelleyFailure $
    Shelley.validateBadInputsUTxO utxo inputsAndCollateral

  {- consumed pp utxo txb = produced pp poolParams txb -}
  runValidationTransMaybe fromShelleyMAFailure $
    ShelleyMA.validateValueNotConservedUTxO pp utxo stakepools txb

  {-   adaID ∉ supp mint tx   -}
  runValidationStaticTransMaybe fromShelleyMAFailure $
    ShelleyMA.validateTriesToForgeADA txb

  let outputs = txouts txb
  {-   ∀ txout ∈ txouts txb, getValuetxout ≥ inject (uxoEntrySizetxout ∗ coinsPerUTxOWord p) -}
  runValidation $ validateOutputTooSmallUTxO pp outputs

  {-   ∀ txout ∈ txouts txb, serSize (getValue txout) ≤ maxValSize pp   -}
  runValidation $ validateOutputTooBigUTxO pp outputs

  {- ∀ ( _ ↦ (a,_)) ∈ txoutstxb,  a ∈ Addrbootstrap → bootstrapAttrsSize a ≤ 64 -}
  runValidationStaticTransMaybe fromShelleyFailure $
    Shelley.validateOutputBootAddrAttrsTooBig outputs

  netId <- liftSTS $ asks networkId

  {- ∀(_ → (a, _)) ∈ txouts txb, netId a = NetworkId -}
  runValidationStaticTransMaybe fromShelleyFailure $ Shelley.validateWrongNetwork netId txb

  {- ∀(a → ) ∈ txwdrls txb, netId a = NetworkId -}
  runValidationStaticTransMaybe fromShelleyFailure $ Shelley.validateWrongNetworkWithdrawal netId txb

  {- (txnetworkid txb = NetworkId) ∨ (txnetworkid txb = ◇) -}
  runValidationStatic $ validateWrongNetworkInTxBody netId txb

  {- txsize tx ≤ maxTxSize pp -}
  runValidationTransMaybe fromShelleyFailure $ Shelley.validateMaxTxSizeUTxO pp tx

  {-   totExunits tx ≤ maxTxExUnits pp    -}
  runValidation $ validateExUnitsTooBigUTxO pp tx

  {-   ‖collateral tx‖  ≤  maxCollInputs pp   -}
  runValidation $ validateTooManyCollateralInputs pp txb

  trans @(Core.EraRule "UTXOS" era) =<< coerce <$> judgmentContext


whoops :: Bool -> Validation (NonEmpty (UtxoPredicateFailure era)) ()
whoops x = undefined