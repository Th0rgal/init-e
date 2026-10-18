import InitECandidate.Runtime.AuthorizationsRecordScopeOuterPrefix
import InitECandidate.Runtime.AuthorizationsRecordScopeBound
import InitECandidate.Runtime.TrapBodyClock
import InitECandidate.Runtime.AuthorizationsRecordSource
import InitECandidate.Runtime.AuthorizationsCidDeclarationBound
import InitECandidate.Runtime.AuthorizationsCidStoreBound
import InitECandidate.Runtime.FourWordValueShape
import InitECandidate.Runtime.TxScalarU256InputPrefix
import InitECandidate.Runtime.TxScalarU256InputGlobals
import InitECandidate.Runtime.AuthorizationsRStoreLastBound
import InitECandidate.Runtime.PanDecCallCheckedContinuationBound
import InitECandidate.Runtime.AuthorizationsRTailSource
import InitECandidate.Runtime.FourWordStoreInputPrefix
import InitECandidate.Runtime.AuthorizationsLastScalarBound
import InitECandidate.Runtime.NamedGlobalFrame
import InitECandidate.Runtime.AuthorizationsTailSource
import InitECandidate.Runtime.TxScalarU256DeclarationInputBound
import InitECandidate.Runtime.TxScalarU256InputBound
import InitECandidate.Runtime.OriginalTxScalarU256Code
import InitECandidate.Runtime.PanThreeWordShapeLookup
import InitECandidate.Runtime.PanDecCallStraightBound
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A normally completed arity guard and record body preserve the outer slice array. -/
theorem authorization_entry_check_normal_outer_prefix {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (record records index array count input inputLength scratch frame outerArray outerCount : BitVec 64) (ceiling inputLimit : Nat)
    (recordAddress : record = records + index * 120#64)
    (recordsLocal : state.locals.lookup (ofString "recs") = some (.val (.word records)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (before : array.toNat + count.toNat * 16 ≤ record.toNat ∨ record.toNat + 120 ≤ array.toNat) (fits : record.toNat + 120 < 2^64)
    (entryLocal : state.locals.lookup (ofString "ent") = some (.rStruct [.val (.word array),.val (.word count)]))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (arrayBelowFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (budget : 6 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ≤ state.clock)
    (outerValid : RlpSliceInputPrefix state outerArray input inputLength outerCount.toNat)
    (outerBelow : outerArray.toNat + outerCount.toNat * 16 ≤ frame.toNat)
    (outerBeforeRecord : outerArray.toNat + outerCount.toNat * 16 ≤ record.toNat)
    (run : evaluateHOLFiniteState state authorizationEntryCheck = (none,final)) :
    RlpSliceInputPrefix final outerArray input inputLength outerCount.toNat := by
  let guard : ProgHOL 64 := .ite (.cmp .notEqual (.rfield 1 (.var .local (ofString "ent"))) (.const 6))
    (.raise (ofString "TxErr") (.const 20)) .skip
  by_cases six : count = 6#64
  · have condition : @evalHOLExact 64 F _ state.toExact
        (fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .notEqual (.rfield 1 (.var .local (ofString "ent"))) (.const 6)) = some (.val (.word 0)) := by
      simp [evalHOLExact,entryLocal,Compiler.Encoders.Asm.wordCmpHOL,six]
    have passed : evaluateHOLFiniteState state guard = (none,state) := by
      rw [show guard = .ite (.cmp .notEqual (.rfield 1 (.var .local (ofString "ent"))) (.const 6))
        (.raise (ofString "TxErr") (.const 20)) .skip from rfl,evaluateHOLFiniteState_ite,condition]
      simp [evaluateHOLFiniteState_skip]
    rw [source_authorization_entry_check,evaluateHOLFiniteState_seq_line780,passed] at run
    exact authorization_record_scope_normal_outer_prefix state final record records index array count input inputLength scratch frame
      outerArray outerCount ceiling inputLimit recordAddress recordsLocal indexLocal before fits entryLocal valid (by rw [six]; decide)
      inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena arrayBelowFrame budget outerValid outerBelow outerBeforeRecord run
  · have condition : @evalHOLExact 64 F _ state.toExact
        (fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .notEqual (.rfield 1 (.var .local (ofString "ent"))) (.const 6)) = some (.val (.word 1)) := by
      simp [evalHOLExact,entryLocal,Compiler.Encoders.Asm.wordCmpHOL] <;> simp_all
    have failed : evaluateHOLFiniteState state guard =
        evaluateHOLFiniteState state (.raise (ofString "TxErr") (.const 20)) := by
      rw [show guard = .ite (.cmp .notEqual (.rfield 1 (.var .local (ofString "ent"))) (.const 6))
        (.raise (ofString "TxErr") (.const 20)) .skip from rfl,evaluateHOLFiniteState_ite,condition]
      simp
    have terminal := evaluate_raise_terminal state (ofString "TxErr") (.const 20)
    have safe := evaluate_raise_no_timeout state (ofString "TxErr") (.const 20)
    have clock := clockPreserving_raise (σ := F) (ofString "TxErr") (.const 20) state
    rw [source_authorization_entry_check,evaluateHOLFiniteState_seq_line780,failed] at run
    cases raised : evaluateHOLFiniteState state (.raise (ofString "TxErr") (.const 20)) with
    | mk result post =>
      rw [raised] at terminal safe clock run
      cases result with
      | none => exact False.elim (terminal rfl)
      | some result =>
        cases run

#print axioms authorization_entry_check_normal_outer_prefix
end InitECandidate.Runtime
