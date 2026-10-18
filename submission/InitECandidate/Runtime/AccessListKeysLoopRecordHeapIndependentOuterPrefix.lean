import InitECandidate.Runtime.AccessListKeysLoopHeapIndependentOuterPrefix
import InitECandidate.Runtime.AccessListKeysLoopHeapOtherLocal
import InitECandidate.Runtime.AccessListRecordScopePrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Both nested key traversal and record completion retain the outer input slices. -/
theorem access_keys_loop_and_record_normal_heap_independent_outer_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count buffer input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (outerArray outerCount outerInput outerLength : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerAbove : ceiling ≤ outerArray.toNat)
    (outerBeforeBuffer : outerArray.toNat + outerCount.toNat * 16 ≤ buffer.toNat)
    (valid : AccessKeysLoopWitness state array count buffer input inputLength scratch frame ceiling)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayAbove : ceiling ≤ array.toNat)
    (arrayBeforeBuffer : array.toNat + count.toNat * 16 ≤ buffer.toNat)
    (aligned : buffer.toNat % 8 = 0) (fits : buffer.toNat + count.toNat * 32 ≤ 2^64)
    (budget : (count.toNat - valid.index.toNat) *
      (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) ≤ state.clock)
    (records outerIndex address : BitVec 64)
    (recordsLocal : state.locals.lookup (ofString "recs") = some (.val (.word records)))
    (outerIndexLocal : state.locals.lookup (ofString "i") = some (.val (.word outerIndex)))
    (addressLocal : state.locals.lookup (ofString "addr") = some (.val (.word address)))
    (outerBeforeRecord : outerArray.toNat + outerCount.toNat * 16 ≤ (records + outerIndex * 24#64).toNat)
    (recordFits : (records + outerIndex * 24#64).toNat + 24 < 2^64)
    (run : evaluateHOLFiniteState state accessKeysLoopAndRecord = (none,post)) :
    RlpSliceInputPrefix post outerArray outerInput outerLength outerCount.toNat := by
  rw [source_access_keys_loop_and_record,evaluateHOLFiniteState_seq_line780] at run
  cases loopRun : evaluateHOLFiniteState state accessKeysLoop with
  | mk result middle =>
    rw [loopRun] at run
    cases result with
    | some result => cases run
    | none =>
      obtain ⟨result,output,evaluated,_,_,_,done,_⟩ := evaluate_access_keys_loop_heap_independent_outer_prefix_bounded state
        array count buffer input inputLength scratch frame ceiling inputLimit outerArray outerCount outerInput outerLength outerValid outerAbove outerBeforeBuffer
        valid inputBound limitBound orderedFrame framePositive scratchBelow arrayAbove arrayBeforeBuffer aligned fits budget
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (evaluated.symm.trans loopRun)
      obtain ⟨next,_,kept⟩ := done rfl
      have locals : ∀ key : MlS, key ≠ ofString "j" → key ≠ ofString "k" →
          output.locals.lookup key = state.locals.lookup key := by
        intro key different notScoped
        exact access_keys_loop_normal_heap_other_local state output key different notScoped
          array count buffer input inputLength scratch frame ceiling inputLimit valid inputBound limitBound orderedFrame framePositive
          scratchBelow arrayAbove arrayBeforeBuffer aligned fits budget loopRun
      exact access_record_scope_normal_input_prefix output post records outerIndex address buffer array count outerArray outerCount outerInput outerLength
        ((locals _ (by decide) (by decide)).trans recordsLocal)
        ((locals _ (by decide) (by decide)).trans outerIndexLocal)
        ((locals _ (by decide) (by decide)).trans addressLocal)
        next.bufferLocal next.listLocal kept outerBeforeRecord recordFits run

#print axioms access_keys_loop_and_record_normal_heap_independent_outer_prefix
end InitECandidate.Runtime
