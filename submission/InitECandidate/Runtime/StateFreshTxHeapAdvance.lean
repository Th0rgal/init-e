import InitECandidate.Runtime.HeapAdvanceRelation
import InitECandidate.Runtime.StateFreshTxRuntimeBound
import InitECandidate.Runtime.OriginalStateFreshTxCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private theorem tableReturned : ReturnedRel HeapAdvance (sourceFunctionBody Guest.guestFn_htab_new) :=
 returnedRel_heapAdvance_of_heapRel (NormalRel.returned htabNew_normalRel)

/-- The seven assignment-form constructors and pointer stores preserve the
heap frontier on every continuing outcome, independently of available fuel. -/
theorem state_fresh_tx_sequence_heap_advance (tables : List (Nat×Nat×Nat)) (tail : ProgHOL 64)
 (tailRel : NormalRel HeapAdvance tail) : NormalRel HeapAdvance (stateFreshTxConstructorSequence tables tail) := by
 induction tables with
 | nil => exact tailRel
 | cons item rest ih =>
  obtain ⟨width,capacity,offset⟩:=item
  unfold stateFreshTxConstructorSequence
  exact normalRel_seq heapAdvance_preorder
   (normalRel_local_call heapAdvance_preorder _ _ _ _ _ _ originalRuntimeCode_htabNew_lookup tableReturned)
   (normalRel_seq heapAdvance_preorder (heapAdvance_leaf rfl) ih)

/-- Complete original state_fresh_tx heap preservation, allowing its actual
updates to ts and journal_n. No room, fuel or successful-callee premise. -/
theorem state_fresh_tx_heap_advance : NormalRel HeapAdvance (sourceFunctionBody Guest.guestFn_state_fresh_tx) := by
 rw [source_stateFreshTx_body]
 apply normalRel_seq heapAdvance_preorder
 · exact normalRel_global_call heapAdvance_preorder _ _ _ _ _ _ originalRuntimeCode_allocation_lookup
    (returnedRel_heapAdvance_of_heapRel alloc_returnedRel) (heapAdvance_update _ (by decide))
 apply normalRel_seq heapAdvance_preorder (heapAdvance_leaf rfl)
 apply normalRel_decCall heapAdvance_preorder _ _ _ _ _ _ _ originalRuntimeCode_htabNew_lookup tableReturned
 apply normalRel_seq heapAdvance_preorder (heapAdvance_leaf rfl)
 exact state_fresh_tx_sequence_heap_advance stateFreshTxRemainingTables _ (heapAdvance_leaf rfl)

/-- The installed discard call inherits the actual body's heap contract. -/
theorem state_fresh_tx_call_heap_advance : NormalRel HeapAdvance
 (.call (some (none,none)) (ofString "state_fresh_tx") []) :=
 normalRel_discard_call heapAdvance_preorder _ _ _ _ _ originalRuntimeCode_stateFreshTx_lookup
  (NormalRel.returned state_fresh_tx_heap_advance)

/-- A normal returned call supplies the aligned capped heap needed by the
next actual system-transaction call. -/
theorem state_fresh_tx_call_normal_heap {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (code : s.code=originalRuntimeCode) (heap : StateInitHeapReady s)
 (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "state_fresh_tx") [])=(none,post)) :
 StateInitHeapReady post := by
 have rel:=normalRel_apply state_fresh_tx_call_heap_advance (X:=s) (by rw [run];exact Or.inl rfl) code
 rw [run] at rel
 obtain ⟨p,hp,al,cap⟩:=heap
 obtain ⟨q,hq,_,aq,cq⟩:=rel p hp al cap
 exact ⟨q,hq,aq,cq⟩
#print axioms state_fresh_tx_sequence_heap_advance
#print axioms state_fresh_tx_heap_advance
#print axioms state_fresh_tx_call_heap_advance
#print axioms state_fresh_tx_call_normal_heap
end InitECandidate.Runtime
