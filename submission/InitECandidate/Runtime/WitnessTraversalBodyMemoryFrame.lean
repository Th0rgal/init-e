import InitECandidate.Runtime.WitnessTraversalLoopMemoryFrame
import InitECandidate.Runtime.WitnessTraversalReturnedHeap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
theorem return_local_memory_frame {F : Type} (s post : PanSemStateFiniteExact 64 F) (name : MlS) (value : ValueHOL 64)
 (run : evaluateHOLFiniteState s (.return (.var .local name))=(some (.returned value),post)) : post.memory=s.memory := by
 rw [evaluateHOLFiniteState_return] at run
 split at run
 · simp at run
 · split at run
   · obtain ⟨_,rfl⟩:=Prod.mk.inj run;rfl
   · simp at run

theorem witness_traversal_tail_returned_memory {F : Type} (layout : WitnessTraversalLayout)
 (s post : PanSemStateFiniteExact 64 F) (value : ValueHOL 64)
 (valid : WitnessTraversalInvariant layout s) (budget : witnessTraversalLoopCost layout.inputLimit≤s.clock)
 (run : evaluateHOLFiniteState s (decodeWitnessNodeBodyAt 7)=(some (.returned value),post)) :
 ∀watched : BitVec 64,layout.databaseCeiling≤watched.toNat→watched.toNat<layout.dbHeap.toNat→post.memory watched=s.memory watched := by
 rw [source_decode_witness_node_loop] at run
 obtain ⟨middle,loopRun,returned⟩:=seq_returned_of_nonreturning_first
  (evaluate_while_no_return witnessTraversalCondition decodeWitnessNodeIteration
   (fun state value=>evaluate_noDirectReturn _ witness_traversal_iteration_no_direct_return state value) s) run
 have memory:=witness_traversal_loop_normal_memory layout s middle valid budget loopRun
 rw [return_local_memory_frame middle post (ofString "result") value returned]
 exact memory

theorem witness_traversal_body_returned_memory {F : Type} (layout : WitnessTraversalLayout)
 (s post : PanSemStateFiniteExact 64 F) (scratch heap pointer length : BitVec 64) (value : ValueHOL 64)
 (valid : WitnessTraversalEntryPrecondition layout s scratch heap pointer length)
 (atPointer : s.locals.lookup (ofString "p")=some (.val (.word pointer)))
 (atLength : s.locals.lookup (ofString "n")=some (.val (.word length)))
 (budget : witnessTraversalLoopCost layout.inputLimit≤s.clock)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn__decode_witness_node_body)=(some (.returned value),post)) :
 ∀watched : BitVec 64,layout.databaseCeiling≤watched.toNat→watched.toNat<layout.dbHeap.toNat→post.memory watched=s.memory watched := by
 have agreement:=witness_traversal_entry_scoped s pointer length atPointer atLength
 rw [run] at agreement
 let entered:=witnessTraversalEntry s pointer length
 let output:=(evaluateHOLFiniteState entered (decodeWitnessNodeBodyAt 7)).2
 have inner : evaluateHOLFiniteState entered (decodeWitnessNodeBodyAt 7)=(some (.returned value),output):=Prod.ext agreement.1.symm rfl
 have memory:=witness_traversal_tail_returned_memory layout entered output value
  ⟨scratch,heap,0,1,1,valid.initializes layout s scratch heap pointer length⟩ budget inner
 rw [agreement.2.2.1]
 exact memory
#print axioms return_local_memory_frame
#print axioms witness_traversal_tail_returned_memory
#print axioms witness_traversal_body_returned_memory
end InitECandidate.Runtime
