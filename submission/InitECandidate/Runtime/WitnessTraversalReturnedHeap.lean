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
/-- Normal completion retains the concrete traversal invariant from the actual ranked loop. -/
theorem witness_traversal_loop_normal_invariant {F : Type} (layout : WitnessTraversalLayout)
 (s post : PanSemStateFiniteExact 64 F) (valid : WitnessTraversalInvariant layout s)
 (budget : witnessTraversalLoopCost layout.inputLimit≤s.clock)
 (run : evaluateHOLFiniteState s (.while witnessTraversalCondition decodeWitnessNodeIteration)=(none,post)) :
 WitnessTraversalInvariant layout post := by
 have ceiling := witnessTraversalStateMeasure_bound s layout.frame
 have costBound : witnessTraversalStateMeasure layout.frame s*(witnessTraversalIterationCost layout.inputLimit+1)≤
  witnessTraversalLoopCost layout.inputLimit := Nat.mul_le_mul_right _ (Nat.le_of_lt ceiling)
 have ranked := witness_traversal_ranked_loop layout s (witnessTraversalStateMeasure layout.frame s)
  ⟨valid,rfl⟩ (costBound.trans budget)
 rw [run] at ranked
 obtain ⟨rank,⟨kept,_⟩,_,_⟩ := ranked.2.2.2 rfl
 exact kept

private theorem scoped_dec_word {F : Type} (s : PanSemStateFiniteExact 64 F)
 (name : MlS) (initializer : ExpHOL 64) (body : ProgHOL 64) (word : BitVec 64)
 (evaluated : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) initializer=some (.val (.word word))) :
 Scoped (evaluateHOLFiniteState s (.dec name .one initializer body))
  (evaluateHOLFiniteState (setVarHOLFinite name (.val (.word word)) s) body) := by
 rw [evaluateHOLFiniteState_dec_total]
 simp only [evaluated,shapeOfHOLExact,shapeEqHOL,if_true]
 exact scoped_restore _ _

/-- Original seven local declarations leave exactly the loop-entry global/memory context. -/
theorem witness_traversal_entry_scoped {F : Type} (s : PanSemStateFiniteExact 64 F)
 (pointer length : BitVec 64)
 (atPointer : s.locals.lookup (ofString "p")=some (.val (.word pointer)))
 (atLength : s.locals.lookup (ofString "n")=some (.val (.word length))) :
 Scoped (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn__decode_witness_node_body))
 (evaluateHOLFiniteState (witnessTraversalEntry s pointer length) (decodeWitnessNodeBodyAt 7)) := by
 rw [source_decode_witness_node_entry]
 apply scoped_trans (scoped_dec_word _ _ _ _ 0 rfl)
 apply scoped_trans (scoped_dec_word _ _ _ _ 0 rfl)
 apply scoped_trans (scoped_dec_word _ _ _ _ pointer (by
  simp (config:={decide:=true}) only [evalHOLExact,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,atPointer,if_false]))
 apply scoped_trans (scoped_dec_word _ _ _ _ length (by
  simp (config:={decide:=true}) only [evalHOLExact,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,atLength,if_false]))
 apply scoped_trans (scoped_dec_word _ _ _ _ 1 rfl)
 apply scoped_trans (scoped_dec_word _ _ _ _ 0 rfl)
 apply scoped_trans (scoped_dec_word _ _ _ _ 1 rfl)
 exact scoped_refl _

/-- Callee returns are consumed inside the actual iteration, so the loop cannot return directly. -/
theorem witness_traversal_iteration_no_direct_return : noDirectReturn decodeWitnessNodeIteration=true := by
 decide_cbv

/-- A normally returned actual decoder-loop tail has an aligned capped heap. -/
theorem witness_traversal_tail_returned_heap {F : Type} (layout : WitnessTraversalLayout)
 (s post : PanSemStateFiniteExact 64 F) (value : ValueHOL 64)
 (valid : WitnessTraversalInvariant layout s) (budget : witnessTraversalLoopCost layout.inputLimit≤s.clock)
 (run : evaluateHOLFiniteState s (decodeWitnessNodeBodyAt 7)=(some (.returned value),post)) :
 StateInitHeapReady post := by
 rw [source_decode_witness_node_loop] at run
 obtain ⟨middle,loopRun,returned⟩ := seq_returned_of_nonreturning_first
  (evaluate_while_no_return witnessTraversalCondition decodeWitnessNodeIteration
   (fun state value=>evaluate_noDirectReturn _ witness_traversal_iteration_no_direct_return state value) s) run
 have kept := witness_traversal_loop_normal_invariant layout s middle valid budget loopRun
 obtain ⟨scratch,heap,top,mode,go,state⟩ := kept
 have globals := return_local_globals middle post (ofString "result") value returned
 exact ⟨heap,by rw [globals];exact state.atHeap,state.heapAligned,state.heapBound⟩

/-- The actual original decoder body returns an aligned capped allocator frontier. -/
theorem witness_traversal_body_returned_heap {F : Type} (layout : WitnessTraversalLayout)
 (s post : PanSemStateFiniteExact 64 F) (scratch heap pointer length : BitVec 64) (value : ValueHOL 64)
 (valid : WitnessTraversalEntryPrecondition layout s scratch heap pointer length)
 (atPointer : s.locals.lookup (ofString "p")=some (.val (.word pointer)))
 (atLength : s.locals.lookup (ofString "n")=some (.val (.word length)))
 (budget : witnessTraversalLoopCost layout.inputLimit≤s.clock)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn__decode_witness_node_body)=(some (.returned value),post)) :
 StateInitHeapReady post := by
 have agreement :=  witness_traversal_entry_scoped s pointer length atPointer atLength
 rw [run] at agreement
 let entered := witnessTraversalEntry s pointer length
 let output := (evaluateHOLFiniteState entered (decodeWitnessNodeBodyAt 7)).2
 have inner : evaluateHOLFiniteState entered (decodeWitnessNodeBodyAt 7)=(some (.returned value),output) :=
  Prod.ext agreement.1.symm rfl
 have ready := witness_traversal_tail_returned_heap layout entered output value
  ⟨scratch,heap,0,1,1,valid.initializes layout s scratch heap pointer length⟩ budget inner
 obtain ⟨nextHeap,atHeap,aligned,capped⟩ := ready
 exact ⟨nextHeap,by rw [agreement.2.2.2.1];exact atHeap,aligned,capped⟩

#print axioms witness_traversal_iteration_no_direct_return
#print axioms witness_traversal_tail_returned_heap
#print axioms witness_traversal_body_returned_heap

#print axioms witness_traversal_loop_normal_invariant
#print axioms witness_traversal_entry_scoped
end InitECandidate.Runtime
