import InitECandidate.Runtime.StateInitHeapFloorCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
variable {floor : Nat}
def StateInitHeapFloorForward (floor : Nat) (before after : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
 StateInitHeapFloorGlobals floor before→StateInitHeapFloorGlobals floor after

theorem state_init_heap_floor_forward_preorder : GlobalsPreorder (StateInitHeapFloorForward floor) where
 refl:=fun _ h=>h
 trans:=fun _ _ _ a b h=>b (a h)

theorem state_init_heap_floor_forward_of_heapRel {before after : HolFiniteMapExact MlS (ValueHOL 64)}
 (rel : HeapRel before after) : StateInitHeapFloorForward floor before after := fun ready=>heapFloor_of_rel rel ready

theorem state_init_heap_floor_forward_leaf (program : ProgHOL 64)
 (safe : avoidsGlobalAssignment (ofString "heap_ptr") program=true) : NormalRel (StateInitHeapFloorForward floor) program := by
 unfold NormalRel
 intro F s post result code run continuing ready
 obtain ⟨p,atHeap,aligned,capped,lower⟩:=ready
 have kept:=evaluate_avoidsGlobalAssignment (ofString "heap_ptr") program safe s
 rw [run] at kept
 exact ⟨p,kept.trans atHeap,aligned,capped,lower⟩

theorem state_init_assignment_heap_floor_forward (kind : VarKind) (name function : MlS) (arguments : List (ExpHOL 64))
 (parameters : List (MlS×ShapeHOL)) (body : ProgHOL 64) (shape : ShapeHOL)
 (installed : originalRuntimeCode.lookup function=some (parameters,body,shape))
 (bodyHeap : ReturnedRel HeapRel body) (destination : kind=.local ∨name≠ofString "heap_ptr") :
 NormalRel (StateInitHeapFloorForward floor) (.call (some (some (kind,name),none)) function arguments) := by
 unfold NormalRel
 intro F s post result code run continuing ready
 have control:=evaluate_handlerFree_call_control s (some (kind,name)) function arguments
 rw [run] at control
 rcases continuing with normal|continued|broken|⟨value,returned⟩
 · subst result
   exact state_init_assignment_call_heap_floor s post kind name function arguments parameters body shape installed bodyHeap destination code ready run
 · exact False.elim (control.2.1 continued)
 · exact False.elim (control.1 broken)
 · exact False.elim (control.2.2 value returned)

theorem state_init_alloc_assignment_heap_floor_forward (kind : VarKind) (name : MlS) (arguments : List (ExpHOL 64))
 (destination : kind=.local ∨name≠ofString "heap_ptr") :
 NormalRel (StateInitHeapFloorForward floor) (.call (some (some (kind,name),none)) (ofString "alloc") arguments) :=
 state_init_assignment_heap_floor_forward kind name (ofString "alloc") arguments _ _ _
  originalRuntimeCode_allocation_lookup alloc_returnedRel destination

theorem state_init_table_assignment_heap_floor_forward (name : MlS) (width capacity : BitVec 64) :
 NormalRel (StateInitHeapFloorForward floor) (.call (some (some (.local,name),none)) (ofString "htab_new") [.const width,.const capacity]) :=
 state_init_assignment_heap_floor_forward .local name (ofString "htab_new") _ _ _ _
  originalRuntimeCode_htabNew_lookup (NormalRel.returned htabNew_normalRel) (Or.inl rfl)

theorem state_init_table_declaration_heap_floor_forward (name : MlS) (width capacity : BitVec 64) (tail : ProgHOL 64)
 (tailHeap : NormalRel (StateInitHeapFloorForward floor) tail) :
 NormalRel (StateInitHeapFloorForward floor) (.decCall name .one (ofString "htab_new") [.const width,.const capacity] tail) := by
 apply normalRel_decCall state_init_heap_floor_forward_preorder _ _ _ _ _ _ _ originalRuntimeCode_htabNew_lookup _ tailHeap
 unfold ReturnedRel
 intro F s post value code run ready
 have rel:=normalRel_apply htabNew_normalRel (X:=s) (by rw [run];exact Or.inr (Or.inr (Or.inr ⟨value,rfl⟩))) code
 rw [run] at rel
 exact state_init_heap_floor_forward_of_heapRel rel ready
#print axioms state_init_heap_floor_forward_leaf
#print axioms state_init_assignment_heap_floor_forward
#print axioms state_init_table_declaration_heap_floor_forward
end InitECandidate.Runtime
