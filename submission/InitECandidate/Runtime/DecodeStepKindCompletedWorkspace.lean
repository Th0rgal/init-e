import InitECandidate.Runtime.DecodeStepKindUniformBound
import InitECandidate.Runtime.DecodeStepSlicesCompletedWorkspace
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem decode_step_kind_completed_workspace {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (kind pointer length consumed scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
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
    (budget : decodeStepSlicesCost length.toNat + decodeStepTwoCaseCost inputLimit ≤ s.clock)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (arrayAbove : ceiling ≤ array.toNat) (limitCap : inputLimit ≤ 134217712) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s (decodeStepAt 3) =
      (some (.returned (.rStruct [.val (.word (0 : BitVec 64)),value])),post)) :
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  rcases parsedKind with zero | list
  · subst kind
    by_cases empty : length = 0
    · subst length
      rw [evaluate_decode_step_empty_bytes s pointer consumed atItem] at run
      have same := (Prod.mk.inj run).2
      rw [← same]
      exact ⟨scratchGlobal,frameGlobal⟩
    · rw [evaluate_decode_step_nonempty_bytes s pointer length consumed empty code atItem] at run
      exact False.elim (evaluate_discard_call_no_return s (ofString "mpt_fail") [.const 4] _ (congrArg Prod.fst run))
  · subst kind
    rw [evaluate_decode_step_list_dispatch s pointer length consumed atItem] at run
    exact decode_step_slices_completed_workspace s post pointer length consumed scratch frame array ceiling inputLimit
      atItem noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
      budget heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray arrayAbove limitCap value run

#print axioms decode_step_kind_completed_workspace
end InitECandidate.Runtime
