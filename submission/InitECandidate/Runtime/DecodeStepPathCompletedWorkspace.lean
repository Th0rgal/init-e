import InitECandidate.Runtime.DecodeStepLeafBranchWorkspace
import InitECandidate.Runtime.DecodeStepPathDispatchBound
import InitECandidate.Runtime.ReturnedPairTagSyntax
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every actual returned extension suffix is a stack push, including all its
original stores and the allocation call. No successful allocation is assumed. -/
theorem decode_step_extension_returned_tag {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s decodeStepExtensionSuffix = (some (.returned value),post)) :
    ∃ record, value = .rStruct [.val (.word (1 : BitVec 64)),record] := by
  have certified : returnedPairTagSyntax [1] decodeStepExtensionSuffix = true := by
    rw [source_decodeStep_extension_suffix,source_decodeStep_extension_record,source_decodeStep_extension_stores]
    rfl
  obtain ⟨tag,record,member,same⟩ := evaluate_returnedPairTagSyntax [1] _ certified s post value run
  have one : tag = 1 := by simpa using member
  subst tag
  exact ⟨record,same⟩

/-- The actual compact continuation returning a completed node restores both
workspace frontiers. An extension cannot masquerade as a completed leaf. -/
theorem decode_step_path_completed_workspace {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array pointer length scratch frame nibs count leaf : BitVec 64) (ceiling inputLimit : Nat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (slice : RlpSliceEntry s array 1 pointer length)
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : length.toNat*((2*length.toNat+1)*15+19)+92637 ≤ s.clock)
    (atPath : s.locals.lookup (ofString "cn") = some
      (.rStruct [.val (.word nibs),.val (.word count),.val (.word leaf)])) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s decodeStepCompactContinuation =
      (some (.returned (.rStruct [.val (.word (0 : BitVec 64)),value])),post)) :
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  by_cases zero : leaf = 0
  · subst leaf
    rw [evaluate_decodeStep_extension_dispatch s nibs count atPath] at run
    obtain ⟨record,same⟩ := decode_step_extension_returned_tag s post _ run
    have firstEq := (List.cons.inj (ValueHOL.rStruct.inj same)).1
    have impossible : (0 : BitVec 64) = 1 := HolWordLab.word.inj (ValueHOL.val.inj firstEq)
    exact False.elim ((by decide : (0 : BitVec 64) ≠ 1) impossible)
  · rw [evaluate_decode_step_leaf_dispatch s nibs count leaf zero atPath] at run
    exact decode_step_leaf_branch_returned_workspace s post array pointer length scratch frame ceiling inputLimit
      atArray slice noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow
      arena budget _ run

#print axioms decode_step_extension_returned_tag
#print axioms decode_step_path_completed_workspace
end InitECandidate.Runtime
