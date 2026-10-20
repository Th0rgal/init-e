import InitECandidate.Runtime.WitnessTraversalUniformBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- Entry geometry and database contents survive an actual call context switch.
Only the callee database local must be installed at its concrete table. -/
theorem WitnessTraversalEntryPrecondition.with_locals_clock {F : Type} (layout : WitnessTraversalLayout)
    (s : PanSemStateFiniteExact 64 F) (scratch heap pointer length : BitVec 64)
    (valid : WitnessTraversalEntryPrecondition layout s scratch heap pointer length)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (atDb : locals.lookup (ofString "db")=some (.val (.word layout.table))) :
    WitnessTraversalEntryPrecondition layout {s with locals:=locals,clock:=clock} scratch heap pointer length := by
  exact {
    code := valid.code
    atDb := atDb
    atScratch := valid.atScratch
    atFrame := valid.atFrame
    atHeap := valid.atHeap
    framePositive := valid.framePositive
    scratchLower := valid.scratchLower
    scratchBound := valid.scratchBound
    scratchBeforeDatabase := valid.scratchBeforeDatabase
    databaseBeforeFloor := valid.databaseBeforeFloor
    floorBeforeHeap := valid.floorBeforeHeap
    heapBound := valid.heapBound
    heapAligned := valid.heapAligned
    inputRange := valid.inputRange
    inputBound := valid.inputBound
    inputLimitBound := valid.inputLimitBound
    inputBeforeFrame := valid.inputBeforeFrame
    scratchArena := valid.scratchArena
    heapArena := valid.heapArena
    built := by
      obtain ⟨k,sd,c,u,v,o,op,n,b,nb,cb,room,inv,ordered,extent⟩ := valid.built
      exact ⟨k,sd,c,u,v,o,op,n,b,nb,cb,room,inv.transfer rfl rfl rfl rfl,ordered.transfer rfl rfl rfl,extent⟩
    entries := valid.entries
    slices := by
      intro index inside
      obtain ⟨p,n,slice⟩ := valid.slices index inside
      exact ⟨p,n,slice.after_frame s {s with locals:=locals,clock:=clock} layout.dbArray index p n layout.input layout.inputLength rfl rfl rfl⟩
    tableAboveDatabase := valid.tableAboveDatabase
    arrayAboveDatabase := valid.arrayAboveDatabase
    dbHeapBeforeFloor := valid.dbHeapBeforeFloor
    dbArrayEnd := valid.dbArrayEnd
    pointerStart := valid.pointerStart
    pointerEnd := valid.pointerEnd
    pointerNoWrap := valid.pointerNoWrap
    lengthBound := valid.lengthBound
  }
/-- Concrete original decoder-body argument map. -/
def witnessTraversalArguments (table pointer length : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  ((HolFiniteMapExact.empty.update (ofString "db",.val (.word table))).update
    (ofString "p",.val (.word pointer))).update (ofString "n",.val (.word length))

/-- The uniform finite body bound is available at the real call-entry state,
without assuming a bound or successful outcome for the callee. -/
theorem runBounded_witness_traversal_body_entry {F : Type} (layout : WitnessTraversalLayout)
    (s : PanSemStateFiniteExact 64 F) (scratch heap pointer length : BitVec 64)
    (valid : WitnessTraversalEntryPrecondition layout s scratch heap pointer length)
    (budget : witnessTraversalBodySourceCeiling+1≤s.clock) :
    RunBounded (callEntryStateHOLFinite s (witnessTraversalArguments layout.table pointer length))
      (sourceFunctionBody Guest.guestFn__decode_witness_node_body) witnessTraversalBodySourceCeiling := by
  let locals := witnessTraversalArguments layout.table pointer length
  have entered := valid.with_locals_clock layout s scratch heap pointer length locals (s.clock-1)
    (by simp (config:={decide:=true}) [locals,witnessTraversalArguments,HolFiniteMapExact.lookup_update,FUPDATE])
  change WitnessTraversalEntryPrecondition layout (callEntryStateHOLFinite s locals) scratch heap pointer length at entered
  exact runBounded_witness_traversal_body_uniform layout (callEntryStateHOLFinite s locals) scratch heap pointer length entered
    (by simp (config:={decide:=true}) [locals,witnessTraversalArguments,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [locals,witnessTraversalArguments,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by change witnessTraversalBodySourceCeiling≤s.clock-1;omega)
#print axioms WitnessTraversalEntryPrecondition.with_locals_clock
#print axioms runBounded_witness_traversal_body_entry
end InitECandidate.Runtime
