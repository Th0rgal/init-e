import InitECandidate.Runtime.WitnessTraversalStateTransport
import InitECandidate.Runtime.WitnessUnwindModeNormalProgress
import InitECandidate.Runtime.NodedbContentsBetweenFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
 theorem WitnessTraversalState.empty_unwind_preserves {F : Type} (layout : WitnessTraversalLayout)
    (s post : PanSemStateFiniteExact 64 F) (scratch heap mode go : BitVec 64)
    (valid : WitnessTraversalState layout s scratch heap 0 mode go) (unwind : mode=0)
    (run : evaluateHOLFiniteState s decodeWitnessNodeUnwindMode=(none,post)) : WitnessTraversalInvariant layout post := by
  have postEq := witness_unwind_empty_normal_progress s post valid.atTop run
  have domain : post.memaddrs=s.memaddrs := by rw [postEq];rfl
  have endian : post.be=s.be := by rw [postEq];rfl
  have code : post.code=s.code := by rw [postEq];rfl
  have memory : post.memory=s.memory := by rw [postEq];rfl
  have floor:=valid.databaseBeforeFloor
  have heapLo:=valid.floorBeforeHeap
  obtain ⟨builtPost,entriesPost,slicesPost⟩ := nodedb_contents_after_between_frame s post layout.table layout.dbHeap layout.dbArray
    layout.total layout.input layout.inputLength heap layout.databaseCeiling valid.built valid.entries valid.slices
    valid.tableAboveDatabase valid.arrayAboveDatabase (by have h:=valid.dbHeapBeforeFloor;omega)
    (by have h:=valid.dbArrayEnd;have d:=valid.dbHeapBeforeFloor;omega) domain endian code (by intro address lo hi;rw [memory])
  have other (name : MlS) (different : name≠ofString "go") : post.locals.lookup name=s.locals.lookup name := by
    rw [postEq]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have atGo : post.locals.lookup (ofString "go")=some (.val (.word (0#64))) := by
    simp [postEq,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atMode : post.locals.lookup (ofString "mode")=some (.val (.word (0#64))) := by
    rw [other _ (by decide),valid.atMode,unwind]
    rfl
  have delivered : ∃ node : BitVec 64, post.locals.lookup (ofString "result")=some (.val (.word node)) ∧
      (node=0 ∨ (layout.persistentFloor≤node.toNat ∧ node.toNat+32≤heap.toNat)) ∧
      WitnessResultAboveStack post layout.input layout.inputLength 0 node layout.persistentFloor scratch.toNat := by
    obtain ⟨node,atNode,envelope,_⟩ := valid.delivered unwind
    exact ⟨node,(other _ (by decide)).trans atNode,envelope,Or.inr ⟨node,Nat.le_refl _,.nil⟩⟩
  refine ⟨scratch,heap,0,0,0,?_⟩
  exact WitnessTraversalState.after_components layout s post scratch heap 0 mode go scratch heap 0 0 0 valid domain code
    ((other _ (by decide)).trans valid.atDb) atGo ((other _ (by decide)).trans valid.atTop) atMode
    (by rw [postEq];exact valid.atScratch) (by rw [postEq];exact valid.atFrame) (by rw [postEq];exact valid.atHeap)
    valid.scratchLower valid.scratchBound (Nat.le_refl _) valid.heapBound valid.heapAligned builtPost entriesPost slicesPost
    .nil .nil (Or.inl rfl) (Or.inl rfl) (by intro bad;cases bad) (by intro bad;cases bad) (fun _ => delivered)
#print axioms WitnessTraversalState.empty_unwind_preserves
end InitECandidate.Runtime
