import InitECandidate.Runtime.WitnessTraversalEntryContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- Concrete database/layout transport after a read-only actual prefix and selection of a contained database slice. -/
theorem WitnessTraversalEntryPrecondition.after_read {F : Type} (layout : WitnessTraversalLayout)
 (s next : PanSemStateFiniteExact 64 F) (scratch heap pointer length selected size : BitVec 64)
 (valid : WitnessTraversalEntryPrecondition layout s scratch heap pointer length)
 (memory : next.memory=s.memory) (globals : next.globals=s.globals)
 (installed : next.code=s.code) (domain : next.memaddrs=s.memaddrs) (endian : next.be=s.be)
 (atDb : next.locals.lookup (ofString "db")=some (.val (.word layout.table)))
 (pointerStart : layout.input.toNat≤selected.toNat)
 (pointerEnd : selected.toNat+size.toNat≤layout.input.toNat+layout.inputLength.toNat)
 (pointerNoWrap : selected.toNat+size.toNat<2^64)
 (lengthBound : size.toNat≤layout.inputLength.toNat) :
 WitnessTraversalEntryPrecondition layout next scratch heap selected size := by
  exact {
    code := installed.trans valid.code
    atDb := atDb
    atScratch := by rw [globals]; exact valid.atScratch
    atFrame := by rw [globals]; exact valid.atFrame
    atHeap := by rw [globals]; exact valid.atHeap
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
    scratchArena := by rw [domain]; exact valid.scratchArena
    heapArena := by rw [domain]; exact valid.heapArena
    built := by
      obtain ⟨k,sd,c,u,v,o,op,n,b,nb,cb,room,inv,ordered,extent⟩ := valid.built
      exact ⟨k,sd,c,u,v,o,op,n,b,nb,cb,room,inv.congr domain endian installed (by intro off ho; exact congrFun memory _) (by intro address inside; exact congrFun memory _),ordered.transfer memory domain endian,extent⟩
    entries := valid.entries.after_read memory domain endian
    slices := by
      intro index inside
      obtain ⟨p,n,slice⟩ := valid.slices index inside
      exact ⟨p,n,slice.after_frame s next layout.dbArray index p n layout.input layout.inputLength domain (congrFun memory _) (congrFun memory _)⟩
    tableAboveDatabase := valid.tableAboveDatabase
    arrayAboveDatabase := valid.arrayAboveDatabase
    dbHeapBeforeFloor := valid.dbHeapBeforeFloor
    dbArrayEnd := valid.dbArrayEnd
    pointerStart := pointerStart
    pointerEnd := pointerEnd
    pointerNoWrap := pointerNoWrap
    lengthBound := lengthBound
  }

#print axioms WitnessTraversalEntryPrecondition.after_read
end InitECandidate.Runtime
