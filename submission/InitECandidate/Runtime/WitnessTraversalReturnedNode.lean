import InitECandidate.Runtime.WitnessTraversalStoppedLoop
import InitECandidate.Runtime.WitnessTraversalReturnedHeap
import InitECandidate.Runtime.HtabFindSlotReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

theorem witness_traversal_loop_normal_delivery {F : Type} (layout : WitnessTraversalLayout)
 (s post : PanSemStateFiniteExact 64 F) (valid : WitnessTraversalInvariant layout s)
 (stop : s.locals.lookup (ofString "go")=some (.val (.word (0#64)))→s.locals.lookup (ofString "mode")=some (.val (.word (0#64))))
 (budget : witnessTraversalLoopCost layout.inputLimit≤s.clock)
 (run : evaluateHOLFiniteState s (.while witnessTraversalCondition decodeWitnessNodeIteration)=(none,post)) :
 ∃node : BitVec 64,post.locals.lookup (ofString "result")=some (.val (.word node)) ∧(node=0 ∨(layout.persistentFloor≤node.toNat ∧node.toNat+32≤33806089496)) := by
 have ceiling:=witnessTraversalStateMeasure_bound s layout.frame
 have costBound : witnessTraversalStateMeasure layout.frame s*(witnessTraversalIterationCost layout.inputLimit+1)≤witnessTraversalLoopCost layout.inputLimit := Nat.mul_le_mul_right _ (Nat.le_of_lt ceiling)
 have checked:=witness_traversal_ranked_loop_stopped layout s (witnessTraversalStateMeasure layout.frame s) ⟨valid,rfl⟩ stop (costBound.trans budget)
 rw [run] at checked
 obtain ⟨rank,⟨⟨⟨scratch,heap,top,mode,go,state⟩,_⟩,stopped⟩,_,condition⟩:=checked.2.2.2 rfl
 rcases condition with condition | impossible
 · have atGoZero : post.locals.lookup (ofString "go")=some (.val (.word (0#64))) := by
    rcases state.goBits with zero | one
    · rw [state.atGo,zero];rfl
    · have atGo:=state.atGo
      rw [one] at atGo
      change post.locals.lookup (ofString "go")=some (.val (.word (1#64))) at atGo
      have evaluated : evalHOLFinite post (h:=fun a=>Classical.propDecidable (post.memaddrs a)) witnessTraversalCondition=some (.val (.word (1#64))) := by
       simp [witnessTraversalCondition,evalHOLFinite,evalHOLExact,atGo,Compiler.Encoders.Asm.wordCmpHOL]
      rw [evaluated] at condition
      cases condition
   have modeZero : mode=0 := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (state.atMode.symm.trans (stopped atGoZero))))
   obtain ⟨node,atNode,envelope,_⟩:=state.delivered modeZero
   exact ⟨node,atNode,envelope.elim Or.inl (fun h=>Or.inr ⟨h.1,h.2.trans state.heapBound⟩)⟩
 · exact False.elim impossible

theorem witness_traversal_body_returned_node {F : Type} (layout : WitnessTraversalLayout)
 (s post : PanSemStateFiniteExact 64 F) (scratch heap pointer length : BitVec 64) (value : ValueHOL 64)
 (valid : WitnessTraversalEntryPrecondition layout s scratch heap pointer length)
 (atPointer : s.locals.lookup (ofString "p")=some (.val (.word pointer)))
 (atLength : s.locals.lookup (ofString "n")=some (.val (.word length)))
 (budget : witnessTraversalLoopCost layout.inputLimit≤s.clock)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn__decode_witness_node_body)=(some (.returned value),post)) :
 ∃node : BitVec 64,value=.val (.word node) ∧(node=0 ∨(layout.persistentFloor≤node.toNat ∧node.toNat+32≤33806089496)) := by
 have agreement:=witness_traversal_entry_scoped s pointer length atPointer atLength
 rw [run] at agreement
 let entered:=witnessTraversalEntry s pointer length
 let output:=(evaluateHOLFiniteState entered (decodeWitnessNodeBodyAt 7)).2
 have inner : evaluateHOLFiniteState entered (decodeWitnessNodeBodyAt 7)=(some (.returned value),output):=Prod.ext agreement.1.symm rfl
 rw [source_decode_witness_node_loop] at inner
 obtain ⟨middle,loopRun,returned⟩:=seq_returned_of_nonreturning_first
  (evaluate_while_no_return witnessTraversalCondition decodeWitnessNodeIteration
   (fun state value=>evaluate_noDirectReturn _ witness_traversal_iteration_no_direct_return state value) entered) inner
 have initial:=valid.initializes layout s scratch heap pointer length
 obtain ⟨node,atNode,envelope⟩:=witness_traversal_loop_normal_delivery layout entered middle ⟨scratch,heap,0,1,1,initial⟩
  (by intro bad;have one:=initial.atGo;rw [bad] at one;cases one) budget loopRun
 exact ⟨node,return_local_word middle output (ofString "result") node value atNode returned,envelope⟩
#print axioms witness_traversal_loop_normal_delivery
#print axioms witness_traversal_body_returned_node
end InitECandidate.Runtime
