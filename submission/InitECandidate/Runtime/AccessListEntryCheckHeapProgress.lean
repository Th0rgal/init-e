import InitECandidate.Runtime.AccessListEntryCheckBound
import InitECandidate.Runtime.AccessListAddressHeapProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem access_entry_check_heap_progress {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame heapPointer : BitVec 64) (ceiling inputLimit : Nat)
    (entryLocal : state.locals.lookup (ofString "ent") = some (.rStruct [.val (.word array),.val (.word count)]))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (countLimit : inputLimit * 32 < 2^64)
    (heapArena : ∀ address : BitVec 64, heapPointer.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeHeap : input.toNat + inputLength.toNat ≤ heapPointer.toNat)
    (heapAbove : ceiling ≤ heapPointer.toNat)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (budget : (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634) + accessSlotItemCost inputLength.toNat ≤ state.clock)
    (outerIndex : BitVec 64)
    (binding : state.locals.lookup (ofString "i") = some (.val (.word outerIndex)))
    (run : evaluateHOLFiniteState state accessEntryCheck = (none,final)) :
    final.locals.lookup (ofString "i") = some (.val (.word (outerIndex + 1))) ∧
      final.locals.lookup (ofString "lst") = state.locals.lookup (ofString "lst") ∧
      final.locals.lookup (ofString "recs") = state.locals.lookup (ofString "recs") := by
  let guard : ProgHOL 64 := .ite (.cmp .notEqual (.rfield 1 (.var .local (ofString "ent"))) (.const 2))
    (.raise (ofString "TxErr") (.const 19)) .skip
  by_cases six : count = 2#64
  · have condition : @evalHOLExact 64 F _ state.toExact
        (fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .notEqual (.rfield 1 (.var .local (ofString "ent"))) (.const 2)) = some (.val (.word 0)) := by
      simp [evalHOLExact,entryLocal,Compiler.Encoders.Asm.wordCmpHOL,six]
    have passed : evaluateHOLFiniteState state guard = (none,state) := by
      rw [show guard = .ite (.cmp .notEqual (.rfield 1 (.var .local (ofString "ent"))) (.const 2))
        (.raise (ofString "TxErr") (.const 19)) .skip from rfl,evaluateHOLFiniteState_ite,condition]
      simp [evaluateHOLFiniteState_skip]
    rw [source_access_entry_check,evaluateHOLFiniteState_seq_line780,passed] at run
    exact access_address_heap_progress state final array count input inputLength scratch frame heapPointer ceiling inputLimit
      entryLocal valid (by rw [six]; decide) inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
      scratchBelow arena arrayFits arrayAbove heap heapBound countLimit heapArena inputBeforeHeap heapAbove inputBeforeFrame budget outerIndex binding run
  · have condition : @evalHOLExact 64 F _ state.toExact
        (fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .notEqual (.rfield 1 (.var .local (ofString "ent"))) (.const 2)) = some (.val (.word 1)) := by
      simp [evalHOLExact,entryLocal,Compiler.Encoders.Asm.wordCmpHOL] <;> simp_all
    have failed : evaluateHOLFiniteState state guard =
        evaluateHOLFiniteState state (.raise (ofString "TxErr") (.const 19)) := by
      rw [show guard = .ite (.cmp .notEqual (.rfield 1 (.var .local (ofString "ent"))) (.const 2))
        (.raise (ofString "TxErr") (.const 19)) .skip from rfl,evaluateHOLFiniteState_ite,condition]
      simp
    have terminal := evaluate_raise_terminal state (ofString "TxErr") (.const 19)
    have safe := evaluate_raise_no_timeout state (ofString "TxErr") (.const 19)
    have clock := clockPreserving_raise (σ := F) (ofString "TxErr") (.const 19) state
    rw [source_access_entry_check,evaluateHOLFiniteState_seq_line780,failed] at run
    cases raised : evaluateHOLFiniteState state (.raise (ofString "TxErr") (.const 19)) with
    | mk result post =>
      rw [raised] at terminal safe clock run
      cases result with
      | none => exact False.elim (terminal rfl)
      | some result =>
        cases run

#print axioms access_entry_check_heap_progress
end InitECandidate.Runtime
