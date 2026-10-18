import InitECandidate.Runtime.Sha256UnpackLoopMemory
import InitECandidate.Runtime.MarkedHeapReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem shaBlockUnpack_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (initial pointer watched : BitVec 64) (value : ValueHOL 64)
    (atIndex : state.locals.lookup (ofString "i") = some (.val (.word initial)))
    (atPointer : state.locals.lookup (ofString "stp") = some (.val (.word pointer)))
    (small : initial.toNat ≤ 4) (fits : pointer.toNat + 64 ≤ 33806089496)
    (outside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (shaBlockAt 5) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  rw [source_shaBlock_unpack] at run
  obtain ⟨middle,normal,returned⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile _ (by decide) state v) run
  have frame := shaBlockUnpack_loop_normal_memory state middle initial pointer watched atIndex atPointer small fits outside code normal
  have finalMemory := evaluate_readOnly_memory (.return (.const 0)) rfl middle
  rw [returned] at finalMemory
  rw [finalMemory]
  exact frame

theorem shaBlockReset_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (oldIndex pointer watched : BitVec 64) (value : ValueHOL 64)
    (atIndex : state.locals.lookup (ofString "i") = some (.val (.word oldIndex)))
    (atPointer : state.locals.lookup (ofString "stp") = some (.val (.word pointer)))
    (fits : pointer.toNat + 64 ≤ 33806089496)
    (outside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (shaBlockAt 4) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have reset : evaluateHOLFiniteState state (.assign .local (ofString "i") (.const 0)) =
      (none,setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state) := by
    simp [evaluateHOLFiniteState_assign,evalHOLExact,isValidValueHOLExact,lookupKvarHOLExact,atIndex,
      shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite]
  rw [source_shaBlock_reset,evaluateHOLFiniteState_seq_line780,reset] at run
  dsimp only at run
  exact shaBlockUnpack_suffix_returned_memory
    (setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state) post 0 pointer watched value
    (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simpa (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atPointer)
    (by decide) fits outside code run

#print axioms shaBlockUnpack_suffix_returned_memory
#print axioms shaBlockReset_suffix_returned_memory
end InitECandidate.Runtime
