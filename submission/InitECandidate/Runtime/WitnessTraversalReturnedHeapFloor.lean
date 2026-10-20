import InitECandidate.Runtime.WitnessTraversalReturnedHeap
import InitECandidate.Runtime.StateInitHeapCallNormal
import InitECandidate.Runtime.WitnessTraversalBodyBound
import InitECandidate.Runtime.NoDirectReturn
import InitECandidate.Runtime.PanWhileNoReturn
import InitECandidate.Runtime.AllocationFramedGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
/-- A normally returned actual decoder-loop tail has an aligned capped heap. -/
theorem witness_traversal_tail_returned_heap_floor {F : Type} (layout : WitnessTraversalLayout)
 (s post : PanSemStateFiniteExact 64 F) (value : ValueHOL 64)
 (valid : WitnessTraversalInvariant layout s) (budget : witnessTraversalLoopCost layout.inputLimit≤s.clock)
 (run : evaluateHOLFiniteState s (decodeWitnessNodeBodyAt 7)=(some (.returned value),post)) :
 (∃nextHeap : BitVec 64,post.globals.lookup (ofString "heap_ptr")=some (.val (.word nextHeap)) ∧nextHeap.toNat%8=0 ∧nextHeap.toNat≤33806089496 ∧layout.persistentFloor≤nextHeap.toNat) := by
 rw [source_decode_witness_node_loop] at run
 obtain ⟨middle,loopRun,returned⟩ := seq_returned_of_nonreturning_first
  (evaluate_while_no_return witnessTraversalCondition decodeWitnessNodeIteration
   (fun state value=>evaluate_noDirectReturn _ witness_traversal_iteration_no_direct_return state value) s) run
 have kept := witness_traversal_loop_normal_invariant layout s middle valid budget loopRun
 obtain ⟨scratch,heap,top,mode,go,state⟩ := kept
 have globals := return_local_globals middle post (ofString "result") value returned
 exact ⟨heap,by rw [globals];exact state.atHeap,state.heapAligned,state.heapBound,state.floorBeforeHeap⟩

/-- The actual original decoder body returns an aligned capped allocator frontier. -/
theorem witness_traversal_body_returned_heap_floor {F : Type} (layout : WitnessTraversalLayout)
 (s post : PanSemStateFiniteExact 64 F) (scratch heap pointer length : BitVec 64) (value : ValueHOL 64)
 (valid : WitnessTraversalEntryPrecondition layout s scratch heap pointer length)
 (atPointer : s.locals.lookup (ofString "p")=some (.val (.word pointer)))
 (atLength : s.locals.lookup (ofString "n")=some (.val (.word length)))
 (budget : witnessTraversalLoopCost layout.inputLimit≤s.clock)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn__decode_witness_node_body)=(some (.returned value),post)) :
 (∃nextHeap : BitVec 64,post.globals.lookup (ofString "heap_ptr")=some (.val (.word nextHeap)) ∧nextHeap.toNat%8=0 ∧nextHeap.toNat≤33806089496 ∧layout.persistentFloor≤nextHeap.toNat) := by
 have agreement :=  witness_traversal_entry_scoped s pointer length atPointer atLength
 rw [run] at agreement
 let entered := witnessTraversalEntry s pointer length
 let output := (evaluateHOLFiniteState entered (decodeWitnessNodeBodyAt 7)).2
 have inner : evaluateHOLFiniteState entered (decodeWitnessNodeBodyAt 7)=(some (.returned value),output) :=
  Prod.ext agreement.1.symm rfl
 have ready := witness_traversal_tail_returned_heap_floor layout entered output value
  ⟨scratch,heap,0,1,1,valid.initializes layout s scratch heap pointer length⟩ budget inner
 obtain ⟨nextHeap,atHeap,aligned,capped,floor⟩ := ready
 exact ⟨nextHeap,by rw [agreement.2.2.2.1];exact atHeap,aligned,capped,floor⟩

#print axioms witness_traversal_iteration_no_direct_return
#print axioms witness_traversal_tail_returned_heap_floor
#print axioms witness_traversal_body_returned_heap_floor

#print axioms witness_traversal_loop_normal_invariant
#print axioms witness_traversal_entry_scoped
end InitECandidate.Runtime
