import InitECandidate.Runtime.AccessListKeysLoopRecordBound
import InitECandidate.Runtime.AccessListKeysLoopHeapBound
import InitECandidate.Runtime.PanSeqStraightBound
import InitECandidate.Runtime.PanSequenceTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_access_keys_loop_and_record_heap_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count buffer input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : AccessKeysLoopWitness state array count buffer input inputLength scratch frame ceiling)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayAbove : ceiling ≤ array.toNat)
    (arrayBeforeBuffer : array.toNat + count.toNat * 16 ≤ buffer.toNat)
    (aligned : buffer.toNat % 8 = 0) (fits : buffer.toNat + count.toNat * 32 ≤ 2^64)
    (budget : (count.toNat - valid.index.toNat) *
      (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state accessKeysLoopAndRecord
    state.clock ≤ evaluated.2.clock + (count.toNat - valid.index.toNat) *
        (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  obtain ⟨result,post,run,cost,remaining,noTimeout,_,_⟩ := evaluate_access_keys_loop_heap_bounded state
    array count buffer input inputLength scratch frame ceiling inputLimit valid inputBound limitBound orderedFrame framePositive
    scratchBelow arrayAbove arrayBeforeBuffer aligned fits budget
  have supported : straightLine accessRecordScope = true := by
    simp only [accessRecordScope,accessKeysLoopAndRecord,accessAt,authorizationNext,sourceFunctionBody,
      InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
    rfl
  have bound := evaluate_sequence_straight_bounded state accessKeysLoop accessRecordScope
    ((count.toNat - valid.index.toNat) * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651))
    (by rw [run]; exact ⟨cost,remaining,noTimeout⟩) supported
  rw [source_access_keys_loop_and_record]
  exact bound

#print axioms evaluate_access_keys_loop_and_record_heap_bounded
end InitECandidate.Runtime
