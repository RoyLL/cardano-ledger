{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Cardano.Ledger.Babbage.Rules.Utxos
  where

import Cardano.Ledger.Alonzo.Rules.Utxos
  ( UtxosPredicateFailure (..),
    -- constructValidated,
    validBegin,
    validEnd,
    invalidBegin,
    invalidEnd,
    UtxosEvent,
    (?!##),
    TagMismatchDescription(..),
  )
import Cardano.Ledger.Shelley.Rules.Utxo (UtxoEnv (..), updateUTxOState)
import Cardano.Ledger.Shelley.Rules.Ppup (PPUPEnv (..)) -- , PpupPredicateFailure)  

import Control.Monad.Trans.Reader (asks)
import Control.State.Transition.Extended

import Cardano.Ledger.Era(Era(..),ValidateScript)
import qualified Cardano.Ledger.Core as Core
import qualified Cardano.Ledger.Babbage.Tx as Babbage
import qualified Cardano.Ledger.Babbage.TxBody as Babbage
import qualified Cardano.Ledger.Babbage.PParams as Babbage
import qualified Cardano.Ledger.Alonzo.Scripts as Alonzo
import qualified Cardano.Ledger.Mary.Value as Mary
import Cardano.Ledger.Alonzo.Tx(IsValid(..))

import Cardano.Ledger.Babbage.Tx(ValidatedTx(..))
import Cardano.Ledger.BaseTypes(ShelleyBase,systemStart, epochInfo)
import Cardano.Binary (ToCBOR (..)) --FromCBOR (..))
import qualified Data.Compact.SplitMap as SplitMap
import Cardano.Ledger.Shelley.LedgerState (PPUPState (..), UTxOState (..),keyRefunds, updateStakeDistribution)
import Cardano.Ledger.Shelley.UTxO (UTxO (..), balance, totalDeposits)

import Cardano.Ledger.Alonzo.PlutusScriptApi
  ( -- CollectError,
    collectTwoPhaseScriptInputs,
    evalScripts,
  )
  
import qualified Data.Map as Map
import qualified Cardano.Ledger.Val as Val

import Cardano.Ledger.Shelley.PParams (Update)
import Cardano.Ledger.Alonzo.TxInfo (ScriptResult (Fails,Passes)) -- ,FailureDescription (..))

import GHC.Records (HasField (..))
import Debug.Trace (traceEvent)
import Data.Maybe.Strict
import Data.Foldable (toList)

-- =====================================================

type ConcreteBabbage era =
  ( Core.Script era ~ Alonzo.Script era,
    Core.Value era ~ Mary.Value (Crypto era),
    Core.TxBody era ~ Babbage.TxBody era,
    Core.PParams era ~ Babbage.PParams era,
    Core.PParamsDelta era ~ Babbage.PParamsUpdate era,
    Core.TxOut era ~ Babbage.TxOut era
  )
  
data BabbageUTXOS era

instance
  forall era.
  ( Era era,
    ConcreteBabbage era,
    Embed (Core.EraRule "PPUP" era) (BabbageUTXOS era),
    Environment (Core.EraRule "PPUP" era) ~ PPUPEnv era,
    State (Core.EraRule "PPUP" era) ~ PPUPState era,
    Signal (Core.EraRule "PPUP" era) ~ Maybe (Update era),
    ValidateScript era,
    ToCBOR (PredicateFailure (Core.EraRule "PPUP" era)) -- Serializing the PredicateFailure
  ) =>
  STS (BabbageUTXOS era)
  where
  type BaseM (BabbageUTXOS era) = ShelleyBase
  type Environment (BabbageUTXOS era) = UtxoEnv era
  type State (BabbageUTXOS era) = UTxOState era
  type Signal (BabbageUTXOS era) = ValidatedTx era
  type PredicateFailure (BabbageUTXOS era) = UtxosPredicateFailure era
  type Event (BabbageUTXOS era) = UtxosEvent era
  transitionRules = [utxosTransition]

utxosTransition ::
  forall era.
  ( ConcreteBabbage era,
    Environment (Core.EraRule "PPUP" era) ~ PPUPEnv era,
    State (Core.EraRule "PPUP" era) ~ PPUPState era,
    Signal (Core.EraRule "PPUP" era) ~ Maybe (Update era),
    Embed (Core.EraRule "PPUP" era) (BabbageUTXOS era),
    ValidateScript era,
    ToCBOR (PredicateFailure (Core.EraRule "PPUP" era)) -- Serializing the PredicateFailure
  ) =>
  TransitionRule (BabbageUTXOS era)
utxosTransition =
  judgmentContext >>= \(TRC (_, _, tx)) -> do
    case getField @"isValid" tx of
      IsValid True -> scriptsValidateTransition
      IsValid False -> scriptsNotValidateTransition

-- ===================================================================

scriptsValidateTransition ::
  forall era.
  ( ValidateScript era,
    ConcreteBabbage era,
    STS(BabbageUTXOS era),
    Environment (Core.EraRule "PPUP" era) ~ PPUPEnv era,
    State (Core.EraRule "PPUP" era) ~ PPUPState era,
    Signal (Core.EraRule "PPUP" era) ~ Maybe (Update era),
    Embed (Core.EraRule "PPUP" era) (BabbageUTXOS era)
  ) =>
  TransitionRule (BabbageUTXOS era)
scriptsValidateTransition = do
  TRC (UtxoEnv slot pp poolParams genDelegs, u@(UTxOState utxo _ _ pup _), tx) <-
    judgmentContext
  let txb = body tx
      refunded = keyRefunds pp txb
      txcerts = toList $ getField @"certs" txb
      depositChange =
        totalDeposits pp (`Map.notMember` poolParams) txcerts Val.<-> refunded
  sysSt <- liftSTS $ asks systemStart
  ei <- liftSTS $ asks epochInfo
  
  let !_ = traceEvent validBegin ()
 
  case collectTwoPhaseScriptInputs ei sysSt pp tx utxo of
    Right sLst ->
      case evalScripts @era tx sLst of
        Fails sss ->
          False
            ?!## ValidationTagMismatch
              (getField @"isValid" tx)
              (FailedUnexpectedly sss)
        Passes -> pure ()
    Left info -> failBecause (CollectErrors info)

  let !_ = traceEvent validEnd ()
  
  ppup' <-
    trans @(Core.EraRule "PPUP" era) $
      TRC
        (PPUPEnv slot pp genDelegs, pup, strictMaybeToMaybe $ getField @"update" txb)

  pure $! updateUTxOState u txb depositChange ppup'

scriptsNotValidateTransition ::
  forall era.
  ( ValidateScript era,
    ConcreteBabbage era,
    STS(BabbageUTXOS era)
  ) =>
  TransitionRule (BabbageUTXOS era)
scriptsNotValidateTransition = do
  TRC (UtxoEnv _ pp _ _, us@(UTxOState utxo _ fees _ _), tx) <- judgmentContext
  let txb = body tx
  sysSt <- liftSTS $ asks systemStart
  ei <- liftSTS $ asks epochInfo

  let !_ = traceEvent invalidBegin ()
  
  case collectTwoPhaseScriptInputs ei sysSt pp tx utxo of
    Right sLst ->
      case evalScripts @era tx sLst of
        Passes -> False ?!## ValidationTagMismatch (getField @"isValid" tx) PassedUnexpectedly
        Fails _sss -> pure ()
    Left info -> failBecause (CollectErrors info)

  let !_ = traceEvent invalidEnd ()
  
      {- utxoKeep = getField @"collateral" txb ⋪ utxo -}
      {- utxoDel  = getField @"collateral" txb ◁ utxo -}
      !(!utxoKeep, !utxoDel) =
        SplitMap.extractKeysSet (unUTxO utxo) (getField @"collateral" txb)
  pure
    $! us
      { _utxo = UTxO utxoKeep,
        _fees = fees <> Val.coin (balance (UTxO utxoDel)),
        _stakeDistro = updateStakeDistribution (_stakeDistro us) (UTxO utxoDel) mempty
      }
