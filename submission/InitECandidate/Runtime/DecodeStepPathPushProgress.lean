import InitECandidate.Runtime.DecodeStepLeafReturnedFlag
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A real push returned by the compact-result continuation must be an extension
record. The leaf alternative returns tag zero and cannot hide a scratch-free push. -/
theorem decode_step_path_push_returned_progress {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (nibs count leaf scratch frame record : BitVec 64)
    (atPath : s.locals.lookup (ofString "cn") = some
      (.rStruct [.val (.word nibs),.val (.word count),.val (.word leaf)]))
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (ordered : frame ≤ scratch) (ticks : 3 ≤ s.clock)
    (run : evaluateHOLFiniteState s decodeStepCompactContinuation =
      (some (.returned (.rStruct [.val (.word (1 : BitVec 64)),.val (.word record)])),post)) :
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word (scratchAllocationEnd scratch 88))) ∧
      frame.toNat ≤ (scratchAllocationEnd scratch 88).toNat ∧
      (scratchAllocationEnd scratch 88).toNat + 88 ≤ scratch.toNat := by
  by_cases zero : leaf = 0
  · subst leaf
    rw [evaluate_decodeStep_extension_dispatch s nibs count atPath] at run
    exact decode_step_extension_suffix_returned_progress s post scratch frame _ scratchGlobal frameGlobal code ordered ticks run
  · rw [evaluate_decode_step_leaf_dispatch s nibs count leaf zero atPath] at run
    obtain ⟨value,shape⟩ := decode_step_leaf_branch_returned_flag s post _ run
    have firstEq := (List.cons.inj (ValueHOL.rStruct.inj shape)).1
    have impossible : (1 : BitVec 64) = 0 := HolWordLab.word.inj (ValueHOL.val.inj firstEq)
    exact False.elim ((by decide : (1 : BitVec 64) ≠ 0) impossible)

#print axioms decode_step_path_push_returned_progress
end InitECandidate.Runtime
