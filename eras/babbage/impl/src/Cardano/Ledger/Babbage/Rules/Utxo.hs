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

-- import Cardano.Ledger.Babbage.Rules.Utxos (BabbageUTXOS)

-- AlonzoUtxoNeeds,
-- FeeNeeds,
-- UtxoDelta (UtxoDelta),

-- genericAlonzoUtxo,

import Cardano.Binary (FromCBOR (..), ToCBOR (..), serialize)
import Cardano.Ledger.Address
  ( Addr (..),
    RewardAcnt,
    getNetwork,
    getRwdNetwork,
  )
import Cardano.Ledger.Alonzo.Data (DataHash, dataHashSize)
import Cardano.Ledger.Alonzo.Rules.Utxo
  ( AlonzoUTXO,
    UtxoEvent (..),
    UtxoPredicateFailure (..),
    fromShelleyFailure,
    fromShelleyMAFailure,
    vKeyLocked,
    validateCollateral,
    validateCollateralContainsNonADA,
    validateExUnitsTooBigUTxO,
    validateInsufficientCollateral,
    validateOutputTooBigUTxO,
    validateOutputTooSmallUTxO,
    validateOutsideForecast,
    validateScriptsNotPaidUTxO,
    validateTooManyCollateralInputs,
    validateWrongNetworkInTxBody,
  )
-- --------------------------------

import Cardano.Ledger.Alonzo.Rules.Utxos (UTXOS, UtxosPredicateFailure (..))
import Cardano.Ledger.Alonzo.Rules.Utxow (UtxowPredicateFail)
import Cardano.Ledger.Alonzo.Scripts (ExUnits (..), Prices, pointWiseExUnits)
import Cardano.Ledger.Alonzo.Tx (ValidatedTx (..), minfee, totExUnits)
import qualified Cardano.Ledger.Alonzo.Tx as Alonzo (ValidatedTx)
import qualified Cardano.Ledger.Alonzo.TxSeq as Alonzo (TxSeq)
import Cardano.Ledger.Alonzo.TxWitness (TxWitness (..), nullRedeemers)
import Cardano.Ledger.Babbage.Collateral (collBalance, feesOK, minCollateral)
import Cardano.Ledger.Babbage.Tx (ValidatedTx (..), txouts, wits)
import Cardano.Ledger.Babbage.TxBody
  ( TxBody (..),
    TxOut,
    collateral',
    collateralReturn',
    totalCollateral',
    txfee',
  )
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
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Era (Era (..), ValidateScript (..))
import qualified Cardano.Ledger.Era as Era
import Cardano.Ledger.Rules.ValidationMode
  ( Inject (..),
    InjectMaybe (..),
    mapMaybeValidation,
    runTest,
    runTestOnSignal,
    runValidation,
    runValidationStatic,
    runValidationStaticTransMaybe,
    runValidationTransMaybe,
  )
import Cardano.Ledger.Shelley.Constraints (UsesPParams)
import qualified Cardano.Ledger.Shelley.LedgerState as Shelley
import qualified Cardano.Ledger.Shelley.Rules.Utxo as Shelley
import Cardano.Ledger.Shelley.Tx (TxIn)
import Cardano.Ledger.Shelley.TxBody (DCert, Wdrl, unWdrl)
import qualified Cardano.Ledger.ShelleyMA.Rules.Utxo as ShelleyMA
  ( UtxoPredicateFailure,
    validateOutsideValidityIntervalUTxO,
    validateTriesToForgeADA,
    validateValueNotConservedUTxO,
  )
import Cardano.Ledger.ShelleyMA.Timelocks (ValidityInterval (..), inInterval)
import Control.Monad.Trans.Reader (asks)
import Control.State.Transition.Extended
  ( Embed (..),
    Rule,
    RuleType (Transition),
    STS (..),
    TRC (..),
    TransitionRule (..),
    judgmentContext,
    liftSTS,
    trans,
    (?!),
  )
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

-- ======================================================

-- | Predicate failure for the Babbage Era
data BabbageUtxoPred era
  = FromAlonzoUtxoFail (UtxoPredicateFailure era) -- Inherited from Alonzo
  | FromAlonzoUtxowFail (UtxowPredicateFail era) -- Not sure this makes sense
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

-- ===============================================
-- Inject instances

instance Inject (UtxoPredicateFailure era) (BabbageUtxoPred era) where
  inject = FromAlonzoUtxoFail

instance Inject (UtxowPredicateFail era) (BabbageUtxoPred era) where
  inject = FromAlonzoUtxowFail

instance Inject (BabbageUtxoPred era) (BabbageUtxoPred era) where
  inject = id

instance
  Inject (PredicateFailure (Core.EraRule "PPUP" era)) (PredicateFailure (Core.EraRule "UTXOS" era)) =>
  Inject (ShelleyMA.UtxoPredicateFailure era) (BabbageUtxoPred era)
  where
  inject = FromAlonzoUtxoFail . inject

instance
  Inject (PredicateFailure (Core.EraRule "PPUP" era)) (PredicateFailure (Core.EraRule "UTXOS" era)) =>
  Inject (Shelley.UtxoPredicateFailure era) (BabbageUtxoPred era)
  where
  inject = FromAlonzoUtxoFail . inject

-- =======================================================

-- | feesOK can differ from Era to Era, as new notions of fees arise. This is the Babbage version
--   See: Figure 2: Functions related to fees and collateral, in the Babbage specification
--   In the spec feesOK is a boolean function. Because wee need to handle predicate failures
--   in the implementaion, it is coded as a TransitionRule. It will return () if it succeeds,
--   and raise an error (rather than return) if any of the required parts are False.
--   This version is generic in that it can be lifted to any PredicateFailure type that
--   embeds BabbageUtxoPred era. This makes it possibly useful in future Eras.

{-
feesOK ::
  forall era utxo.
  ( Era era,
    ValidateScript era, -- isTwoPhaseScriptAddress
    Core.Tx era ~ ValidatedTx era,
    Core.Witnesses era ~ TxWitness era,
    Core.TxBody era ~ TxBody era,
    FeeNeeds era
  ) =>
  (BabbageUtxoPred era -> PredicateFailure (utxo era)) ->
  Core.PParams era ->
  Core.Tx era ->
  UTxO era ->
  Validation (NonEmpty (UtxoPredicateFailure era)) ()
feesOK lift pp tx (UTxO utxo) = do
  let txb = getField @"body" tx
      theFee = txfee' txb -- Coin supplied to pay fees
      minimumFee = minfee @era pp tx
      lift2 = lift . FromAlonzoUtxoFail
  -- Part 1  (minfee pp tx ≤ txfee tx )
  (minimumFee <= theFee) ?! lift2 (FeeTooSmallUTxO minimumFee theFee)

  -- Part 2 (txrdmrs tx /= ◇ ⇒ ... )
  unless (nullRedeemers . txrdmrs' . wits $ tx) $ do
    -- Part 3 ((∀(a, , ) ∈ range (collInputs txb ◁ utxo), paymentHK a ∈ Addr^{vkey})
    let collateral = collateralInputs' txb SplitMap.◁ utxo
    -- UTxO restricted to the inputs allocated to pay the Fee
    all vKeyLocked collateral
      ?! lift2 (ScriptsNotPaidUTxO (UTxO (SplitMap.filter (not . vKeyLocked) collateral)))

    -- Part 4 (balance ≥ minCollateral tx pp)
    let valbalance = collBalance txb (UTxO utxo)
        balance = coin valbalance
    balance >= minCollateral txb pp ?! lift2 (InsufficientCollateral balance (minCollateral txb pp))

    -- Part 5 (adaOnly balance)
    adaOnly valbalance ?! lift2 (CollateralContainsNonADA valbalance)

    -- Part 6 ((txcoll tx 6 = 3) ⇒ balance = txcoll tx)
    case collateralReturn' txb of
      SNothing -> pure ()
      SJust _txout -> balance == total ?! lift (UnequalCollateralReturn balance total)
        where
          total = totalCollateral' txb

    -- Part 7 (collInputs tx 6 = ∅)
    not (Set.null (collateralInputs' txb)) ?! lift2 NoCollateralInputs

    pure ()

-}

-- ========================================================

{-

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

-}
whoops :: Bool -> Validation (NonEmpty (UtxoPredicateFailure era)) ()
whoops x = undefined
