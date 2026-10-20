import InitECandidate.Runtime.StateInitHeapFloorForward
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
variable {floor : Nat}
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem state_init_final_tail_heap_floor_forward : NormalRel (StateInitHeapFloorForward floor)
 (stateInitSpineDrop 26 (sourceFunctionBody Guest.guestFn_state_init)) := by
 rw [source_state_init_final_tail]
 apply normalRel_seq state_init_heap_floor_forward_preorder
  (state_init_alloc_assignment_heap_floor_forward .global (ofString "sk_buf") [.const 64] (Or.inr (by decide)))
 unfold stateInitJournalTail
 exact normalRel_seq state_init_heap_floor_forward_preorder (state_init_heap_floor_forward_leaf _ (by decide))
  (normalRel_seq state_init_heap_floor_forward_preorder
   (state_init_alloc_assignment_heap_floor_forward .global (ofString "journal") _ (Or.inr (by decide)))
   (state_init_heap_floor_forward_leaf _ (by decide)))

theorem state_init_table_list_heap_floor_forward (tables : List (Nat×Nat×Nat)) (tail : ProgHOL 64)
 (tailHeap : NormalRel (StateInitHeapFloorForward floor) tail) : NormalRel (StateInitHeapFloorForward floor) (blockCtorSeq tables tail) := by
 induction tables with
 | nil=>exact tailHeap
 | cons entry rest ih=>
  obtain ⟨width,capacity,offset⟩:=entry
  unfold blockCtorSeq
  exact normalRel_seq state_init_heap_floor_forward_preorder
   (state_init_table_assignment_heap_floor_forward (ofString "t") (BitVec.ofNat 64 width) (BitVec.ofNat 64 capacity))
   (normalRel_seq state_init_heap_floor_forward_preorder (state_init_heap_floor_forward_leaf _ rfl) ih)

theorem state_init_block_tail_heap_floor_forward : NormalRel (StateInitHeapFloorForward floor)
 (stateInitSpineDrop 8 (sourceFunctionBody Guest.guestFn_state_init)) := by
 rw [source_stateInit_block]
 unfold blockSegment
 apply normalRel_seq state_init_heap_floor_forward_preorder
  (state_init_alloc_assignment_heap_floor_forward .global (ofString "bs") [.const 80] (Or.inr (by decide)))
 apply normalRel_seq state_init_heap_floor_forward_preorder (state_init_heap_floor_forward_leaf _ rfl)
 apply state_init_table_list_heap_floor_forward
 apply normalRel_seq state_init_heap_floor_forward_preorder (state_init_heap_floor_forward_leaf _ rfl)
 apply normalRel_seq state_init_heap_floor_forward_preorder (state_init_heap_floor_forward_leaf _ rfl)
 exact state_init_table_list_heap_floor_forward blockTablesLast _ state_init_final_tail_heap_floor_forward

theorem state_init_fixed_suffix_heap_floor_forward : NormalRel (StateInitHeapFloorForward floor)
 (stateInitSpineDrop 6 (sourceFunctionBody Guest.guestFn_state_init)) := by
 rw [source_state_init_storage_table]
 exact state_init_table_declaration_heap_floor_forward (ofString "t") 32 64 _
  (normalRel_seq state_init_heap_floor_forward_preorder (state_init_heap_floor_forward_leaf _ rfl) state_init_block_tail_heap_floor_forward)

/-- All actual table/block/scratch/journal constructors preserve a successful
initializer's heap endpoint, while permitting their other real global writes. -/
theorem state_init_fixed_suffix_returned_heap_floor {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (value : ValueHOL 64) (code : s.code=originalRuntimeCode)
 (ready : StateInitHeapFloorReady floor s)
 (run : evaluateHOLFiniteState s (stateInitSpineDrop 6 (sourceFunctionBody Guest.guestFn_state_init))=(some (.returned value),post)) :
 StateInitHeapFloorReady floor post := by
 have rel:=normalRel_apply (state_init_fixed_suffix_heap_floor_forward (floor:=floor)) (X:=s)
  (by rw [run];exact Or.inr (Or.inr (Or.inr ⟨value,rfl⟩))) code
 rw [run] at rel
 exact rel ready
#print axioms state_init_final_tail_heap_floor_forward
#print axioms state_init_table_list_heap_floor_forward
#print axioms state_init_block_tail_heap_floor_forward
#print axioms state_init_fixed_suffix_heap_floor_forward
#print axioms state_init_fixed_suffix_returned_heap_floor
end InitECandidate.Runtime
