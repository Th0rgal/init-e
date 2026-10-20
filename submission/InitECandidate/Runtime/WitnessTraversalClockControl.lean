import InitECandidate.Runtime.WitnessTraversalInvariant
import InitECandidate.Runtime.NoLoopControlWhile
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000000
set_option cbv.warning false
/-- The invariant depends on runtime data, not the proof clock. -/
theorem WitnessTraversalState.after_clock {F : Type} (layout : WitnessTraversalLayout)
    (s : PanSemStateFiniteExact 64 F) (scratch heap top mode go : BitVec 64)
    (valid : WitnessTraversalState layout s scratch heap top mode go) (clock : Nat) :
    WitnessTraversalState layout {s with clock:=clock} scratch heap top mode go := by
  have keepStack (frontier : BitVec 64)
      (stack : WitnessAllocationStack s layout.input layout.inputLength frontier layout.persistentFloor scratch.toNat top) :
      WitnessAllocationStack {s with clock:=clock} layout.input layout.inputLength frontier layout.persistentFloor scratch.toNat top :=
    stack.after_frame s {s with clock:=clock} layout.input layout.inputLength frontier top layout.persistentFloor scratch.toNat
      rfl frontier scratch.toNat (Nat.le_refl _) (Nat.le_refl _) (by intro w lo hi;rfl)
  exact {
    code := valid.code
    atDb := valid.atDb
    atTop := valid.atTop
    atMode := valid.atMode
    atGo := valid.atGo
    atScratch := valid.atScratch
    atFrame := valid.atFrame
    atHeap := valid.atHeap
    framePositive := valid.framePositive
    scratchLower := valid.scratchLower
    scratchBound := valid.scratchBound
    scratchAligned := valid.scratchAligned
    scratchBeforeDatabase := valid.scratchBeforeDatabase
    databaseBeforeFloor := valid.databaseBeforeFloor
    floorBeforeHeap := valid.floorBeforeHeap
    heapBound := valid.heapBound
    heapAligned := valid.heapAligned
    inputRange := valid.inputRange
    inputBound := valid.inputBound
    inputLimitBound := valid.inputLimitBound
    inputBeforeFrame := valid.inputBeforeFrame
    inputBeforeFloor := valid.inputBeforeFloor
    scratchArena := valid.scratchArena
    heapArena := valid.heapArena
    built := by
      obtain ⟨k,sd,c,u,v,o,op,n,b,nb,cb,room,inv,ordered,extent⟩ := valid.built
      exact ⟨k,sd,c,u,v,o,op,n,b,nb,cb,room,inv.transfer rfl rfl rfl rfl,ordered.transfer rfl rfl rfl,extent⟩
    entries := valid.entries
    slices := by
      intro index inside
      obtain ⟨p,n,slice⟩ := valid.slices index inside
      exact ⟨p,n,slice.after_frame s {s with clock:=clock} layout.dbArray index p n layout.input layout.inputLength rfl rfl rfl⟩
    tableAboveDatabase := valid.tableAboveDatabase
    arrayAboveDatabase := valid.arrayAboveDatabase
    dbHeapBeforeFloor := valid.dbHeapBeforeFloor
    dbArrayEnd := valid.dbArrayEnd
    stack := keepStack heap valid.stack
    scratchChain := valid.scratchChain.after_frame s {s with clock:=clock} top layout.scratchUpper scratch.toNat scratch.toNat (Nat.le_refl _) (by intro w lo hi;rfl)
    modes := valid.modes
    goBits := valid.goBits
    decodeInput := valid.decodeInput
    resolveSelector := valid.resolveSelector
    delivered := by
      intro modeZero
      obtain ⟨node,atNode,envelope,above⟩ := valid.delivered modeZero
      refine ⟨node,atNode,envelope,?_⟩
      rcases above with zero | ⟨saved,before,stack⟩
      · exact Or.inl zero
      · exact Or.inr ⟨saved,before,keepStack saved stack⟩
  }
/-- The actual body cannot emit loop break or continue, even through opaque
callee execution; checked calls use the real source control semantics. -/
theorem witness_iteration_no_loop_control : noLoopControlWhile decodeWitnessNodeIteration=true := by
  decide_cbv

theorem witness_iteration_outcome_control {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s decodeWitnessNodeIteration).1≠some .break ∧
    (evaluateHOLFiniteState s decodeWitnessNodeIteration).1≠some .continue :=
  evaluate_noLoopControlWhile decodeWitnessNodeIteration witness_iteration_no_loop_control s
#print axioms WitnessTraversalState.after_clock
#print axioms witness_iteration_no_loop_control
#print axioms witness_iteration_outcome_control
end InitECandidate.Runtime
