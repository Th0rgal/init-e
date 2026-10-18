import InitECandidate.Runtime.AccessListKeysLoopOtherLocal
import InitECandidate.Runtime.AccessListRecordProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem access_keys_loop_and_record_progress {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count buffer input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : AccessKeysLoopWitness state array count buffer input inputLength scratch frame ceiling)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayBeforeFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (arrayBeforeBuffer : array.toNat + count.toNat * 16 ≤ buffer.toNat)
    (aligned : buffer.toNat % 8 = 0) (fits : buffer.toNat + count.toNat * 32 ≤ 2^64)
    (budget : (count.toNat - valid.index.toNat) *
      (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) ≤ state.clock)
    (outerIndex : BitVec 64)
    (binding : state.locals.lookup (ofString "i") = some (.val (.word outerIndex)))
    (run : evaluateHOLFiniteState state accessKeysLoopAndRecord = (none,post)) :
    post.locals.lookup (ofString "i") = some (.val (.word (outerIndex + 1))) := by
  rw [source_access_keys_loop_and_record,evaluateHOLFiniteState_seq_line780] at run
  cases loopRun : evaluateHOLFiniteState state accessKeysLoop with
  | mk result middle =>
    rw [loopRun] at run
    cases result with
    | some result => cases run
    | none =>
      have same := access_keys_loop_normal_other_local state middle (ofString "i") (by decide) (by decide)
        array count buffer input inputLength scratch frame ceiling inputLimit valid inputBound limitBound orderedFrame framePositive
        scratchBelow arrayBeforeFrame arrayBeforeBuffer aligned fits budget loopRun
      exact accessRecordScope_increments middle post outerIndex (same.trans binding) run

#print axioms access_keys_loop_and_record_progress
theorem access_keys_loop_and_record_locals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count buffer input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : AccessKeysLoopWitness state array count buffer input inputLength scratch frame ceiling)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayBeforeFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (arrayBeforeBuffer : array.toNat + count.toNat * 16 ≤ buffer.toNat)
    (aligned : buffer.toNat % 8 = 0) (fits : buffer.toNat + count.toNat * 32 ≤ 2^64)
    (budget : (count.toNat - valid.index.toNat) *
      (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) ≤ state.clock)
    (run : evaluateHOLFiniteState state accessKeysLoopAndRecord = (none,post)) :
    post.locals.lookup (ofString "lst") = state.locals.lookup (ofString "lst") ∧
      post.locals.lookup (ofString "recs") = state.locals.lookup (ofString "recs") := by
  rw [source_access_keys_loop_and_record,evaluateHOLFiniteState_seq_line780] at run
  cases loopRun : evaluateHOLFiniteState state accessKeysLoop with
  | mk result middle =>
    rw [loopRun] at run
    cases result with
    | some result => cases run
    | none =>
      have listSame := access_keys_loop_normal_other_local state middle (ofString "lst") (by decide) (by decide)
        array count buffer input inputLength scratch frame ceiling inputLimit valid inputBound limitBound orderedFrame framePositive
        scratchBelow arrayBeforeFrame arrayBeforeBuffer aligned fits budget loopRun
      have recordsSame := access_keys_loop_normal_other_local state middle (ofString "recs") (by decide) (by decide)
        array count buffer input inputLength scratch frame ceiling inputLimit valid inputBound limitBound orderedFrame framePositive
        scratchBelow arrayBeforeFrame arrayBeforeBuffer aligned fits budget loopRun
      have tail := access_record_scope_loop_locals middle post run
      exact ⟨tail.1.trans listSame,tail.2.trans recordsSame⟩

#print axioms access_keys_loop_and_record_locals
end InitECandidate.Runtime
