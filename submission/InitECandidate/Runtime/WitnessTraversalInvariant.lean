import InitECandidate.Runtime.WitnessScratchChain
import InitECandidate.Runtime.WitnessSelectedSlot
import InitECandidate.Runtime.WitnessResultAboveStack
import InitECandidate.Runtime.WitnessDecodeModeDatabaseFrame
import InitECandidate.Runtime.WitnessTraversalStateMeasure
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Fixed addresses and input bounds of one original witness traversal. The
scratch ceiling and persistent allocation floor have separate roles. -/
structure WitnessTraversalLayout where
  table : BitVec 64
  dbHeap : BitVec 64
  dbArray : BitVec 64
  total : BitVec 64
  input : BitVec 64
  inputLength : BitVec 64
  frame : BitVec 64
  scratchUpper : Nat
  databaseCeiling : Nat
  persistentFloor : Nat
  inputLimit : Nat

/-- Concrete obligations for one source-loop state. Every execution-mode
contract can read its arguments from these actual locals, globals and cells. -/
structure WitnessTraversalState {F : Type} (layout : WitnessTraversalLayout)
    (s : PanSemStateFiniteExact 64 F) (scratch heap top mode go : BitVec 64) : Prop where
  code : s.code=originalRuntimeCode
  atDb : s.locals.lookup (ofString "db")=some (.val (.word layout.table))
  atTop : s.locals.lookup (ofString "top")=some (.val (.word top))
  atMode : s.locals.lookup (ofString "mode")=some (.val (.word mode))
  atGo : s.locals.lookup (ofString "go")=some (.val (.word go))
  atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch))
  atFrame : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word layout.frame))
  atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  framePositive : 0<layout.frame.toNat
  scratchLower : layout.frame.toNat≤scratch.toNat
  scratchBound : scratch.toNat≤layout.scratchUpper
  scratchBeforeDatabase : layout.scratchUpper≤layout.databaseCeiling
  databaseBeforeFloor : layout.databaseCeiling≤layout.persistentFloor
  floorBeforeHeap : layout.persistentFloor≤heap.toNat
  heapBound : heap.toNat≤33806089496
  heapAligned : heap.toNat%8=0
  inputRange : layout.input.toNat+layout.inputLength.toNat<2^64
  inputBound : layout.inputLength.toNat≤layout.inputLimit
  inputLimitBound : layout.inputLimit≤134217712
  inputBeforeFrame : layout.input.toNat+layout.inputLength.toNat≤layout.frame.toNat
  scratchArena : ∀ address : BitVec 64, layout.frame.toNat≤address.toNat → address.toNat<layout.scratchUpper → s.memaddrs address
  heapArena : ∀ address : BitVec 64, layout.persistentFloor≤address.toNat → address.toNat<33806089496 → s.memaddrs address
  built : NodedbTableAt s layout.table layout.dbHeap layout.total
  entries : HashTableValuesIn layout.table (NodedbSliceTargets layout.dbArray layout.total) s
  slices : RlpSliceInputPrefix s layout.dbArray layout.input layout.inputLength layout.total.toNat
  tableAboveDatabase : layout.databaseCeiling≤layout.table.toNat
  arrayAboveDatabase : layout.databaseCeiling≤layout.dbArray.toNat
  dbHeapBeforeFloor : layout.dbHeap.toNat≤layout.persistentFloor
  dbArrayEnd : layout.dbArray.toNat+layout.total.toNat*16≤layout.dbHeap.toNat
  stack : WitnessAllocationStack s layout.input layout.inputLength heap layout.persistentFloor scratch.toNat top
  scratchChain : WitnessScratchChain s layout.scratchUpper scratch.toNat top
  modes : mode=0 ∨ mode=1 ∨ mode=2
  goBits : go=0 ∨ go=1
  decodeInput : mode=1 → ∃ pointer length : BitVec 64,
    s.locals.lookup (ofString "cur_p")=some (.val (.word pointer)) ∧
    s.locals.lookup (ofString "cur_n")=some (.val (.word length)) ∧
    layout.input.toNat≤pointer.toNat ∧ pointer.toNat+length.toNat≤layout.input.toNat+layout.inputLength.toNat ∧
    pointer.toNat+length.toNat<2^64 ∧ length.toNat≤layout.inputLength.toNat
  resolveSelector : mode=2 → top≠0 ∧ WitnessSelectedSlot s top
  delivered : mode=0 → ∃ node : BitVec 64,
    s.locals.lookup (ofString "result")=some (.val (.word node)) ∧
    (node=0 ∨ (layout.persistentFloor≤node.toNat ∧ node.toNat+32≤heap.toNat)) ∧
    WitnessResultAboveStack s layout.input layout.inputLength top node layout.persistentFloor scratch.toNat

def WitnessTraversalInvariant {F : Type} (layout : WitnessTraversalLayout) (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ scratch heap top mode go : BitVec 64, WitnessTraversalState layout s scratch heap top mode go

/-- A resolve state supplies the actual readable record slot and an enclosed
original-input slice, rather than a caller-supplied evaluation callback. -/
theorem WitnessTraversalState.resolve_arguments {F : Type} (layout : WitnessTraversalLayout)
    (s : PanSemStateFiniteExact 64 F) (scratch heap top mode go : BitVec 64)
    (valid : WitnessTraversalState layout s scratch heap top mode go) (resolve : mode=2) :
    ∃ array slot pointer length : BitVec 64,
      s.memory (top+24)=.word array ∧ s.memaddrs (top+24) ∧
      s.locals.lookup (ofString "slot")=some (.val (.word slot)) ∧ slot.toNat<17 ∧
      RlpSliceInputEntry s array slot pointer length layout.input layout.inputLength ∧ length.toNat≤layout.inputLimit := by
  obtain ⟨nonempty,selected⟩ := valid.resolveSelector resolve
  have physical := valid.stack.physical s layout.input layout.inputLength heap top layout.persistentFloor scratch.toNat
  cases physical with
  | nil => exact False.elim (nonempty rfl)
  | cons above record ordered tail =>
    obtain ⟨array,slot,pointer,length,atArray,domain,atSlot,slotBound,entry,lengthBound⟩ :=
      witness_selected_physical_record_slice s top _ layout.input layout.inputLength heap layout.persistentFloor record selected
    exact ⟨array,slot,pointer,length,atArray,domain,atSlot,slotBound,entry,lengthBound.trans valid.inputBound⟩

/-- The loop invariant entails the uniformly finite state-rank bound; its
preservation and initialization are separate actual-execution obligations. -/
theorem WitnessTraversalInvariant.measure_bound {F : Type} (layout : WitnessTraversalLayout)
    (s : PanSemStateFiniteExact 64 F) (valid : WitnessTraversalInvariant layout s) :
    witnessTraversalStateMeasure layout.frame s < (((2^64-1)/88)+1)*decodeWitnessMeasureLayer :=
  witnessTraversalStateMeasure_bound s layout.frame

#print axioms WitnessTraversalState.resolve_arguments
#print axioms WitnessTraversalInvariant.measure_bound
end InitECandidate.Runtime
