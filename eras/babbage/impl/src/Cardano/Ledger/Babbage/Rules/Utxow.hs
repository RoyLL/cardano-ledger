{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}


module Cardano.Ledger.Babbage.Rules.Utxow
  where

import Cardano.Ledger.Babbage.Rules.Utxo
  ( BabbageUTXO,
    BabbageUtxoPred (FromAlonzoUtxoFail, FromAlonzoUtxowFail),
  )  
import Cardano.Ledger.Babbage.Rules.Utxos(ConcreteBabbage)  
import Cardano.Ledger.Alonzo.Rules.Utxow
  ( missingRequiredDatums,
    hasExactSetOfRedeemers,
    requiredSignersAreWitnessed,
    ppViewHashesMatch,
    witsVKeyNeeded,
    AlonzoEvent,
  )

import qualified Cardano.Ledger.Shelley.Rules.Utxow as Shelley
import Cardano.Ledger.Shelley.Rules.Utxow
  ( validateNeededWitnesses,
  )  
import Cardano.Ledger.AuxiliaryData(ValidateAuxiliaryData)
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Era(Era(..),ValidateScript(..))
import Cardano.Crypto.DSIGN.Class(Signable)
import Cardano.Ledger.Crypto(DSIGN,HASH)
import Cardano.Crypto.Hash.Class(Hash)
import Cardano.Ledger.Hashes(EraIndependentTxBody)
import Control.State.Transition.Extended
  ( Embed (..),
    -- Rule,
    -- RuleType (Transition),
    STS (..),
    TRC (..),
    TransitionRule,
    judgmentContext,
    liftSTS,
    trans,
    -- (?!),
  )
-- import Cardano.Ledger.Alonzo.TxWitness(TxWitness(..))
import Cardano.Ledger.Alonzo.Tx(ValidatedTx(..))
import Cardano.Ledger.Shelley.Rules.Utxo (UtxoEnv (..))
import Cardano.Ledger.Shelley.LedgerState ( UTxOState (..), witsFromTxWitnesses,)
import Cardano.Ledger.Rules.ValidationMode(Inject(..), runTest, runTestOnSignal) -- ,Test )
import GHC.Records(HasField(..))
import Cardano.Ledger.BaseTypes
  ( ShelleyBase,
    -- StrictMaybe (..),
    quorum,
    -- strictMaybeToMaybe,
  )
import Control.Monad.Trans.Reader (asks)
import Cardano.Ledger.Babbage.PParams(PParams,PParams'(..))
import Cardano.Ledger.Alonzo.Rules.Utxow(UtxowPredicateFail)

-- ========================================

data BabbageUTXOW era

-- ==============================================================
-- Here we define the transtion function, using reusable tests.
-- The tests are very generic and reusable, but the transition
-- function is very specific to the Babbage Era.

-- | A very specialized transitionRule function for the Babbage Era.
babbageUtxowTransition ::
  forall era.
  ( ValidateScript era,
    ValidateAuxiliaryData era (Crypto era),
    -- Fix some Core types to the Babbage Era
    ConcreteBabbage era, 
    Core.Tx era ~ ValidatedTx era,
    -- Core.Witnesses era ~ TxWitness era,
    Core.PParams era ~ PParams era,

    Inject (Shelley.UtxowPredicateFailure era) (PredicateFailure (BabbageUTXOW era)),
    Inject (UtxowPredicateFail era) (PredicateFailure (BabbageUTXOW era)),

    Signable (DSIGN (Crypto era)) (Hash (HASH (Crypto era)) EraIndependentTxBody),
    -- Allow UTXOW to call UTXO
    Embed (Core.EraRule "UTXO" era) ( BabbageUTXOW era),
    Environment (Core.EraRule "UTXO" era) ~ UtxoEnv era,
    State (Core.EraRule "UTXO" era) ~ UTxOState era,
    Signal (Core.EraRule "UTXO" era) ~ ValidatedTx era,

    Eq (PredicateFailure (Core.EraRule "UTXOS" era)),
    Show (PredicateFailure (Core.EraRule "UTXOS" era))
  ) =>
  TransitionRule ( BabbageUTXOW era)
babbageUtxowTransition = do
  (TRC (UtxoEnv slot pp stakepools genDelegs, u, tx)) <- judgmentContext

  {-  (utxo,_,_,_ ) := utxoSt  -}
  {-  txb := txbody tx  -}
  {-  txw := txwits tx  -}
  {-  witsKeyHashes := { hashKey vk | vk ∈ dom(txwitsVKey txw) }  -}
  let utxo = _utxo u
      txbody = getField @"body" (tx :: Core.Tx era)
      witsKeyHashes = witsFromTxWitnesses @era tx

  {-  { h | (_ → (a,_,h)) ∈ txins tx ◁ utxo, isNonNativeScriptAddress tx a} = dom(txdats txw)   -}
  runTest $ missingRequiredDatums utxo tx txbody

  {-  dom (txrdmrs tx) = { rdptr txb sp | (sp, h) ∈ scriptsNeeded utxo tx,
                           h ↦ s ∈ txscripts txw, s ∈ Scriptph2}     -}
  runTest $ hasExactSetOfRedeemers utxo tx txbody

  {-  THIS DOES NOT APPPEAR IN THE SPEC as a separate check, but
      witsVKeyNeeded must include the reqSignerHashes in the union   -}
  runTestOnSignal $ requiredSignersAreWitnessed txbody witsKeyHashes    

  {-  scriptIntegrityHash txb = hashScriptIntegrity pp (languages txw) (txrdmrs txw)  -}
  runTest $ ppViewHashesMatch tx txbody pp

  -- =============================================================
  -- Above this line are Alonzo generic tests
  -- Below this line are Shelley generic tests
  -- =============================================================
  
  -- check scripts
  {-  ∀ s ∈ range(txscripts txw) ∩ Scriptnative), runNativeScript s tx   -}
  runTestOnSignal $ Shelley.validateFailedScripts tx

  {-  { s | (_,s) ∈ scriptsNeeded utxo tx} = dom(txscripts txw)          -}
  runTest $ Shelley.validateMissingScripts pp utxo tx

  -- check VKey witnesses
  {-  ∀ (vk ↦ σ) ∈ (txwitsVKey txw), V_vk⟦ txbodyHash ⟧_σ                -}
  runTestOnSignal $ Shelley.validateVerifiedWits tx

  {-  witsVKeyNeeded utxo tx genDelegs ⊆ witsKeyHashes                   -}
  runTest $ validateNeededWitnesses witsVKeyNeeded genDelegs utxo tx witsKeyHashes

  -- check metadata hash
  {-   adh := txADhash txb;  ad := auxiliaryData tx                      -}  
  {-  ((adh = ◇) ∧ (ad= ◇)) ∨ (adh = hashAD ad)                          -}
  runTestOnSignal $
    Shelley.validateMetadata pp tx

  -- check genesis keys signatures for instantaneous rewards certificates
  {-  genSig := { hashKey gkey | gkey ∈ dom(genDelegs)} ∩ witsKeyHashes  -}
  {-  { c ∈ txcerts txb ∩ DCert_mir} ≠ ∅  ⇒ (|genSig| ≥ Quorum) ∧ (d pp > 0)  -}
  coreNodeQuorum <- liftSTS $ asks quorum
  runTest $
    Shelley.validateMIRInsufficientGenesisSigs genDelegs coreNodeQuorum witsKeyHashes tx

  -- =============================================================
  -- Below this line are Babbage generic tests
  -- =============================================================
  
  trans @(Core.EraRule "UTXO" era) $
    TRC (UtxoEnv slot pp stakepools genDelegs, u, tx)

-- ================================

instance
  forall era.
  ( ValidateScript era,
    ValidateAuxiliaryData era (Crypto era),
    Signable (DSIGN (Crypto era)) (Hash (HASH (Crypto era)) EraIndependentTxBody),
    -- Fix some Core types to the Babbage Era
    Core.Tx era ~ ValidatedTx era,
    -- Core.Witnesses era ~ TxWitness era,
    ConcreteBabbage era,
    -- Allow UTXOW to call UTXO
    Embed (Core.EraRule "UTXO" era) (BabbageUTXOW era),
    Environment (Core.EraRule "UTXO" era) ~ UtxoEnv era,
    State (Core.EraRule "UTXO" era) ~ UTxOState era,
    Signal (Core.EraRule "UTXO" era) ~ ValidatedTx era,

    Inject (Shelley.UtxowPredicateFailure era) (PredicateFailure (BabbageUTXOW era)),
    Eq (PredicateFailure (Core.EraRule "UTXOS" era)),
    Show (PredicateFailure (Core.EraRule "UTXOS" era))
  ) =>
  STS (BabbageUTXOW era)
  where
  type State (BabbageUTXOW era) = UTxOState era
  type Signal (BabbageUTXOW era) = ValidatedTx era
  type Environment (BabbageUTXOW era) = UtxoEnv era
  type BaseM (BabbageUTXOW era) = ShelleyBase
  type PredicateFailure (BabbageUTXOW era) = BabbageUtxoPred era
  type Event (BabbageUTXOW era) = AlonzoEvent era
  transitionRules = [babbageUtxowTransition]
  initialRules = []
