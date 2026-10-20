import InitECandidate.Runtime.WitnessTraversalEntryContext
import InitECandidate.Runtime.NodedbContentsHeapFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- Concrete initial entry data survive fresh persistent allocations above their
old heap frontier, retaining the original database extent ghost. -/
theorem WitnessTraversalEntryPrecondition.after_heap_frame {F : Type} (layout : WitnessTraversalLayout)
 (s next : PanSemStateFiniteExact 64 F) (scratch heap nextHeap pointer length : BitVec 64)
 (valid : WitnessTraversalEntryPrecondition layout s scratch heap pointer length)
 (domain : next.memaddrs=s.memaddrs) (endian : next.be=s.be) (installed : next.code=s.code)
 (frame : ∀address : BitVec 64,address.toNat<heap.toNat→next.memory address=s.memory address)
 (atDb : next.locals.lookup (ofString "db")=some (.val (.word layout.table)))
 (atScratch : next.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (atFrame : next.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word layout.frame)))
 (atHeap : next.globals.lookup (ofString "heap_ptr")=some (.val (.word nextHeap)))
 (growth : heap.toNat≤nextHeap.toNat) (aligned : nextHeap.toNat%8=0) (capped : nextHeap.toNat≤33806089496) :
 WitnessTraversalEntryPrecondition layout next scratch nextHeap pointer length := by
 have contents := nodedb_contents_after_heap_frame s next layout.table layout.dbHeap layout.dbHeap layout.dbArray
  layout.total layout.input layout.inputLength valid.built valid.entries valid.slices valid.dbArrayEnd (Nat.le_refl _)
  domain endian installed (fun address inside=>frame address (lt_of_lt_of_le inside (valid.dbHeapBeforeFloor.trans valid.floorBeforeHeap)))
 exact {
    code := installed.trans valid.code
    atDb := atDb
    atScratch := atScratch
    atFrame := atFrame
    atHeap := atHeap
    framePositive := valid.framePositive
    scratchLower := valid.scratchLower
    scratchBound := valid.scratchBound
    scratchAligned := valid.scratchAligned
    scratchBeforeDatabase := valid.scratchBeforeDatabase
    databaseBeforeFloor := valid.databaseBeforeFloor
    floorBeforeHeap := valid.floorBeforeHeap.trans growth
    heapBound := capped
    heapAligned := aligned
    inputRange := valid.inputRange
    inputBound := valid.inputBound
    inputLimitBound := valid.inputLimitBound
    inputBeforeFrame := valid.inputBeforeFrame
    inputBeforeFloor := valid.inputBeforeFloor
    scratchArena := by rw [domain];exact valid.scratchArena
    heapArena := by rw [domain];exact valid.heapArena
    built := contents.1
    entries := contents.2.1
    slices := contents.2.2
    tableAboveDatabase := valid.tableAboveDatabase
    arrayAboveDatabase := valid.arrayAboveDatabase
    dbHeapBeforeFloor := valid.dbHeapBeforeFloor
    dbArrayEnd := valid.dbArrayEnd
    pointerStart := valid.pointerStart
    pointerEnd := valid.pointerEnd
    pointerNoWrap := valid.pointerNoWrap
    lengthBound := valid.lengthBound
  }

#print axioms WitnessTraversalEntryPrecondition.after_heap_frame
end InitECandidate.Runtime
