import InitECandidate.Runtime.DecodeStepSlicesPushProgress
import InitECandidate.Runtime.DecodeStepNonemptyBytes
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Both actual parsed RLP kinds are covered: byte strings return an empty
completed node or reject, while a list's returned push consumes scratch. -/
theorem decode_step_kind_push_returned_progress {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (kind pointer length consumed scratch frame array record : BitVec 64) (ceiling inputLimit : Nat)
    (atItem : s.locals.lookup (ofString "it") = some
      (.rStruct [.val (.word kind),.val (.word pointer),.val (.word length),.val (.word consumed)]))
    (parsedKind : kind = 0 ∨ kind = 1)
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : decodeStepSlicesCost length.toNat + decodeStepListPushCost inputLimit ≤ s.clock)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (run : evaluateHOLFiniteState s (decodeStepAt 3) =
      (some (.returned (.rStruct [.val (.word (1 : BitVec 64)),.val (.word record)])),post)) :
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word (scratchAllocationEnd scratch 88))) ∧
      frame.toNat ≤ (scratchAllocationEnd scratch 88).toNat ∧
      (scratchAllocationEnd scratch 88).toNat + 88 ≤ scratch.toNat := by
  rcases parsedKind with zeroKind | listKind
  · subst kind
    by_cases zero : length = 0
    · subst length
      rw [evaluate_decode_step_empty_bytes s pointer consumed atItem] at run
      have values := PanSemResultExact.returned.inj (Option.some.inj (Prod.mk.inj run).1)
      have words := (List.cons.inj (ValueHOL.rStruct.inj values)).1
      have impossible : (0#64) = (1 : BitVec 64) := HolWordLab.word.inj (ValueHOL.val.inj words)
      exact False.elim ((by decide : (0#64) ≠ (1 : BitVec 64)) impossible)
    · rw [evaluate_decode_step_nonempty_bytes s pointer length consumed zero code atItem] at run
      have noReturn := evaluate_discard_call_no_return s (ofString "mpt_fail") [.const 4]
        (.rStruct [.val (.word (1 : BitVec 64)),.val (.word record)])
      exact False.elim (noReturn (congrArg Prod.fst run))
  · subst kind
    rw [evaluate_decode_step_list_dispatch s pointer length consumed atItem] at run
    exact decode_step_slices_push_returned_progress s post pointer length consumed scratch frame array record ceiling inputLimit
      atItem noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget heap
      arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray run

#print axioms decode_step_kind_push_returned_progress
end InitECandidate.Runtime
