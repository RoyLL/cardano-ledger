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

import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Era (Era (..), ValidateScript (..))
-- import qualified Cardano.Ledger.Era as Era
import Control.Monad.Trans.Reader (asks)
import Control.State.Transition.Extended
  ( Embed (..),
    -- Rule,
    -- RuleType (Transition),
    STS (..),
    TRC (..),
    TransitionRule (..),
    judgmentContext,
    liftSTS,
    trans,
    -- (?!),
  )
import Cardano.Ledger.Alonzo.Rules.Utxo
  ( -- AlonzoUTXO,
    UtxoEvent (..),
    UtxoPredicateFailure (..),
    -- fromShelleyFailure,
    -- fromShelleyMAFailure,
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
import Cardano.Ledger.Alonzo.Rules.Utxos(UtxosPredicateFailure (..))
import qualified Cardano.Ledger.Shelley.LedgerState as Shelley
import qualified Cardano.Ledger.Shelley.Rules.Utxo as Shelley
import qualified Cardano.Ledger.ShelleyMA.Rules.Utxo as ShelleyMA
  ( UtxoPredicateFailure,
    validateOutsideValidityIntervalUTxO,
    validateTriesToForgeADA,
    validateValueNotConservedUTxO,
  )
import Cardano.Ledger.Alonzo.Rules.Utxow (UtxowPredicateFail)
import Cardano.Ledger.Coin(Coin(..))

import Cardano.Ledger.Rules.ValidationMode
  ( Inject (..),
    Test,
    runTest,
    runTestOnSignal,
  )
import Validation
import Cardano.Ledger.Alonzo.Tx (ValidatedTx (..), minfee, txouts) -- , totExUnits)
-- import qualified Cardano.Ledger.Alonzo.Tx as Alonzo (ValidatedTx)
import Cardano.Ledger.Babbage.TxBody
  ( TxBody(..),
    txfee',
    collateral',
    totalCollateral' ,
    collateralReturn' ,
  )
import Cardano.Ledger.Shelley.UTxO(UTxO(..))
import Cardano.Ledger.Alonzo.TxWitness (TxWitness (..), nullRedeemers)
import GHC.Records(HasField(getField))
import GHC.Natural(Natural)
import Cardano.Ledger.Alonzo.Scripts(Prices)
import qualified Data.Compact.SplitMap as SplitMap
-- import Control.Monad(unless)
import Data.Foldable (sequenceA_)
import Cardano.Ledger.Babbage.Collateral (collBalance, minCollateral)
import qualified Cardano.Ledger.Val as Val
import Data.Coerce (coerce)
import Data.Maybe.Strict(StrictMaybe(..))
import qualified Data.Set as Set
import Cardano.Ledger.BaseTypes
  ( Network,
    ShelleyBase,
    StrictMaybe (..),
    epochInfoWithErr,
    networkId,
    systemStart,
  )

import Cardano.Ledger.Babbage.Rules.Utxos (BabbageUTXOS,ConcreteBabbage)
import Cardano.Ledger.Babbage.PParams(PParams'(..))
-- ======================================================

data BabbageUTXO era

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
--   in the implementaion, it is coded as a Test. Which is a validation.
--   This version is generic in that it can be lifted to any PredicateFailure type that
--   embeds BabbageUtxoPred era. This makes it possibly useful in future Eras.

feesOK ::
  forall era.
  ( ValidateScript era, -- isTwoPhaseScriptAddress
    Core.Tx era ~ ValidatedTx era,
    Core.Witnesses era ~ TxWitness era,
    Core.TxBody era ~ TxBody era,
    HasField "_minfeeA" (Core.PParams era) Natural,
    HasField "_minfeeB" (Core.PParams era) Natural,
    HasField "_prices" (Core.PParams era) Prices,
    HasField "_collateralPercentage" (Core.PParams era) Natural
  ) =>
  Core.PParams era ->
  Core.Tx era ->
  UTxO era ->
  Test (BabbageUtxoPred era)
feesOK pp tx (UTxO utxo) = do
  let txb = getField @"body" tx
      theFee = txfee' txb -- Coin supplied to pay fees
      minimumFee = minfee @era pp tx
  -- Part 1  (minfee pp tx ≤ txfee tx )
  sequenceA_
   [ failureUnless (minimumFee <= theFee) (inject (FeeTooSmallUTxO @era minimumFee theFee))
   , -- Part 2 (txrdmrs tx /= ◇ ⇒ ... )
     if (nullRedeemers . txrdmrs' . wits $ tx) then pure () else 
            let valbalance = collBalance txb (UTxO utxo)
                balance = Val.coin valbalance
                collat = collateral' txb SplitMap.◁ utxo
                -- collat is the UTxO restricted to the inputs allocated to pay the Fee
             in sequenceA_
                [ -- Part 3 ((∀(a, , ) ∈ range (collInputs txb ◁ utxo), paymentHK a ∈ Addr^{vkey})
                  failureUnless (all vKeyLocked collat)
                                (inject (ScriptsNotPaidUTxO (UTxO (SplitMap.filter (not . vKeyLocked) collat))))
                , -- Part 4 (balance ≥ minCollateral tx pp)
                  failureUnless
                     (balance >= minCollateral txb pp)
                     (inject (InsufficientCollateral @era balance (minCollateral txb pp)))
                , -- Part 5 (adaOnly balance)
                  failureUnless (Val.adaOnly valbalance) (inject (CollateralContainsNonADA @era valbalance))
                , -- Part 6 ((txcoll tx 6 = 3) ⇒ balance = txcoll tx)
                  case collateralReturn' txb of
                    SNothing -> pure ()
                    SJust _txout -> failureUnless (balance == total) (inject (UnequalCollateralReturn @era balance total))
                      where total = totalCollateral' txb
                , -- Part 7 (collInputs tx 6 = ∅)
                  failureUnless (not (Set.null (collateral' txb))) (inject (NoCollateralInputs @era))
                ]
     ]

-- ========================================================

-- | The UTxO transition rule for the Babbage eras.
utxoTransition ::
  forall era.
  ( Era era,
    ValidateScript era,
    ConcreteBabbage era, -- Unlike the Tests, we are only going to use this once, so we fix the Core.XX types
    Core.Tx era ~ ValidatedTx era,
    Core.Witnesses era ~ TxWitness era,
    -- We will use this function int the STS instance for (BabbageUTXO era)
    STS (BabbageUTXO era),
    Environment (BabbageUTXO era) ~ Shelley.UtxoEnv era,
    State (BabbageUTXO era) ~ Shelley.UTxOState era,
    Signal (BabbageUTXO era) ~ ValidatedTx era,
    BaseM (BabbageUTXO era) ~ ShelleyBase,
    PredicateFailure (BabbageUTXO era) ~ BabbageUtxoPred era,
    -- instructions for calling UTXOS from BabbageUTXO
    Embed (Core.EraRule "UTXOS" era) (BabbageUTXO era),
    Environment (Core.EraRule "UTXOS" era) ~ Shelley.UtxoEnv era,
    State (Core.EraRule "UTXOS" era) ~ Shelley.UTxOState era,
    Signal (Core.EraRule "UTXOS" era) ~ Core.Tx era,
    Inject (PredicateFailure (Core.EraRule "PPUP" era)) (PredicateFailure (Core.EraRule "UTXOS" era))
  ) =>
  TransitionRule (BabbageUTXO era)
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
  runTest $
    ShelleyMA.validateOutsideValidityIntervalUTxO slot txb

  sysSt <- liftSTS $ asks systemStart
  ei <- liftSTS $ asks epochInfoWithErr

  {- epochInfoSlotToUTCTime epochInfo systemTime i_f ≠ ◇ -}
  runTest $ validateOutsideForecast ei sysSt tx

  {-   txins txb ≠ ∅   -}
  runTestOnSignal $ Shelley.validateInputSetEmptyUTxO txb

  {-   feesOK pp tx utxo   -}
  runTest $ feesOK pp tx utxo -- Generalizes the fee to small from earlier Era's

  {- inputsAndCollateral = txins txb ∪ collateral txb -}
  {- (txins txb) ∪ (collateral txb) ⊆ dom utxo   -}
  runTest $
    Shelley.validateBadInputsUTxO utxo inputsAndCollateral

  {- consumed pp utxo txb = produced pp poolParams txb -}
  runTest $
    ShelleyMA.validateValueNotConservedUTxO pp utxo stakepools txb

  {-   adaID ∉ supp mint tx   -}
  runTestOnSignal $
    ShelleyMA.validateTriesToForgeADA txb

  let outputs = txouts txb
  {-   ∀ txout ∈ txouts txb, getValuetxout ≥ inject (uxoEntrySizetxout ∗ coinsPerUTxOWord p) -}
  runTest $ validateOutputTooSmallUTxO pp outputs

  {-   ∀ txout ∈ txouts txb, serSize (getValue txout) ≤ maxValSize pp   -}
  runTest $ validateOutputTooBigUTxO pp outputs

  {- ∀ ( _ ↦ (a,_)) ∈ txoutstxb,  a ∈ Addrbootstrap → bootstrapAttrsSize a ≤ 64 -}
  runTestOnSignal $
    Shelley.validateOutputBootAddrAttrsTooBig outputs

  netId <- liftSTS $ asks networkId

  {- ∀(_ → (a, _)) ∈ txouts txb, netId a = NetworkId -}
  runTestOnSignal $ Shelley.validateWrongNetwork netId txb

  {- ∀(a → ) ∈ txwdrls txb, netId a = NetworkId -}
  runTestOnSignal $ Shelley.validateWrongNetworkWithdrawal netId txb

  {- (txnetworkid txb = NetworkId) ∨ (txnetworkid txb = ◇) -}
  runTestOnSignal $ validateWrongNetworkInTxBody netId txb

  {- txsize tx ≤ maxTxSize pp -}
  runTestOnSignal $ Shelley.validateMaxTxSizeUTxO pp tx

  {-   totExunits tx ≤ maxTxExUnits pp    -}
  runTest $ validateExUnitsTooBigUTxO pp tx

  {-   ‖collateral tx‖  ≤  maxCollInputs pp   -}
  runTest $ validateTooManyCollateralInputs pp txb

  trans @(Core.EraRule "UTXOS" era) =<< coerce <$> judgmentContext


--------------------------------------------------------------------------------
-- BabbageUTXO STS
--------------------------------------------------------------------------------

instance
  forall era.
  ( ValidateScript era,
    Era era,
    ValidateScript era,
    ConcreteBabbage era, -- Unlike the Tests, we are only going to use this once, so we fix the Core.XX types
    Core.Tx era ~ ValidatedTx era,
    Core.Witnesses era ~ TxWitness era,
    -- instructions for calling UTXOS from BabbageUTXO
    Embed (Core.EraRule "UTXOS" era) (BabbageUTXO era),
    Environment (Core.EraRule "UTXOS" era) ~ Shelley.UtxoEnv era,
    State (Core.EraRule "UTXOS" era) ~ Shelley.UTxOState era,
    Signal (Core.EraRule "UTXOS" era) ~ Core.Tx era,
    Inject (PredicateFailure (Core.EraRule "PPUP" era)) (PredicateFailure (Core.EraRule "UTXOS" era)),
    Eq (PredicateFailure (Core.EraRule "UTXO" era)),
    Show (PredicateFailure (Core.EraRule "UTXO" era))
  ) =>
  STS (BabbageUTXO era)
  where
  type State (BabbageUTXO era) = Shelley.UTxOState era
  type Signal (BabbageUTXO era) = ValidatedTx era
  type Environment (BabbageUTXO era) = Shelley.UtxoEnv era
  type BaseM (BabbageUTXO era) = ShelleyBase
  type PredicateFailure (BabbageUTXO era) = BabbageUtxoPred era
  type Event (BabbageUTXO era) = UtxoEvent era

  initialRules = []
  transitionRules = [utxoTransition]

instance
  ( Era era,
    STS (BabbageUTXOS era),
    PredicateFailure (Core.EraRule "UTXOS" era) ~ UtxosPredicateFailure era,
    Event (Core.EraRule "UTXOS" era) ~ Event (BabbageUTXOS era)
  ) =>
  Embed (BabbageUTXOS era) (BabbageUTXO era)
  where
  wrapFailed =  FromAlonzoUtxoFail . UtxosFailure 
  wrapEvent = UtxosEvent