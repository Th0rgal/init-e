import InitECandidate.Runtime.WitnessTraversalEntryInvariant
import InitECandidate.Runtime.WitnessTraversalLoopBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original loop and final result return share the finite loop cost. -/
theorem witness_traversal_tail_bounded {F : Type} (layout : WitnessTraversalLayout)
    (s : PanSemStateFiniteExact 64 F) (valid : WitnessTraversalInvariant layout s)
    (budget : witnessTraversalLoopCost layout.inputLimit≤s.clock) :
    RunBounded s (decodeWitnessNodeBodyAt 7) (witnessTraversalLoopCost layout.inputLimit) := by
  obtain ⟨scratch,heap,top,mode,go,stateValid⟩ := valid
  have bounded := witness_traversal_loop_bounded layout s ⟨scratch,heap,top,mode,go,stateValid⟩ budget
  rw [source_decode_witness_node_loop]
  have result : ProgBounded (.return (.var .local (ofString "result"))) 0 := ProgBounded.straight _ rfl
  have joined := RunBounded.seq bounded (by simpa using budget) (fun next run code ticks=>
    RunBounded.ofProg result (code.trans stateValid.code) ticks)
  simpa [witnessTraversalCondition] using joined

/-- The complete original explicit-stack decoder body has a finite source-step
bound from concrete entry geometry and actual typed source arguments. The
seven declarations initialize the proved invariant without spending ticks. -/
theorem runBounded_witness_traversal_body {F : Type} (layout : WitnessTraversalLayout)
    (s : PanSemStateFiniteExact 64 F) (scratch heap pointer length : BitVec 64)
    (valid : WitnessTraversalEntryPrecondition layout s scratch heap pointer length)
    (atPointer : s.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n")=some (.val (.word length)))
    (budget : witnessTraversalLoopCost layout.inputLimit≤s.clock) :
    RunBounded s (sourceFunctionBody Guest.guestFn__decode_witness_node_body) (witnessTraversalLoopCost layout.inputLimit) := by
  have initialized := valid.initializes layout s scratch heap pointer length
  have bounded := witness_traversal_tail_bounded layout (witnessTraversalEntry s pointer length)
    ⟨scratch,heap,0,1,1,initialized⟩ budget
  rw [source_decode_witness_node_entry]
  apply RunBounded.decConst
  apply RunBounded.decConst
  apply RunBounded.decWord (value:=pointer)
  · simp (config:={decide:=true}) [evalHOLExact,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,atPointer]
  apply RunBounded.decWord (value:=length)
  · simp (config:={decide:=true}) [evalHOLExact,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,atLength]
  apply RunBounded.decConst
  apply RunBounded.decConst
  apply RunBounded.decConst
  exact bounded

#print axioms witness_traversal_tail_bounded
#print axioms runBounded_witness_traversal_body
end InitECandidate.Runtime
