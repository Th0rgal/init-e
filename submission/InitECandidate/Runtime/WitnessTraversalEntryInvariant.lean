import InitECandidate.Runtime.WitnessTraversalInvariant
import InitECandidate.Runtime.WitnessTraversalEntrySource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- Concrete entry obligations before the seven original local declarations.
The stack starts empty; no runtime or preservation callback is an assumption. -/
structure WitnessTraversalEntryPrecondition {F : Type} (layout : WitnessTraversalLayout)
    (s : PanSemStateFiniteExact 64 F) (scratch heap pointer length : BitVec 64) : Prop where
  code : s.code=originalRuntimeCode
  atDb : s.locals.lookup (ofString "db")=some (.val (.word layout.table))
  atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch))
  atFrame : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word layout.frame))
  atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  framePositive : 0<layout.frame.toNat
  scratchLower : layout.frame.toNat≤scratch.toNat
  scratchBound : scratch.toNat≤layout.scratchUpper
  scratchAligned : scratch.toNat%8=0
  scratchBeforeDatabase : layout.scratchUpper≤layout.databaseCeiling
  databaseBeforeFloor : layout.databaseCeiling≤layout.persistentFloor
  floorBeforeHeap : layout.persistentFloor≤heap.toNat
  heapBound : heap.toNat≤33806089496
  heapAligned : heap.toNat%8=0
  inputRange : layout.input.toNat+layout.inputLength.toNat<2^64
  inputBound : layout.inputLength.toNat≤layout.inputLimit
  inputLimitBound : layout.inputLimit≤134217712
  inputBeforeFrame : layout.input.toNat+layout.inputLength.toNat≤layout.frame.toNat ∨ layout.scratchUpper≤layout.input.toNat
  inputBeforeFloor : layout.input.toNat+layout.inputLength.toNat≤layout.persistentFloor
  scratchArena : ∀ address : BitVec 64, layout.frame.toNat≤address.toNat → address.toNat<layout.scratchUpper → s.memaddrs address
  heapArena : ∀ address : BitVec 64, layout.persistentFloor≤address.toNat → address.toNat<33806089496 → s.memaddrs address
  built : NodedbTableAt s layout.table layout.dbHeap layout.total
  entries : HashTableValuesIn layout.table (NodedbSliceTargets layout.dbArray layout.total) s
  slices : RlpSliceInputPrefix s layout.dbArray layout.input layout.inputLength layout.total.toNat
  tableAboveDatabase : layout.databaseCeiling≤layout.table.toNat
  arrayAboveDatabase : layout.databaseCeiling≤layout.dbArray.toNat
  dbHeapBeforeFloor : layout.dbHeap.toNat≤layout.persistentFloor
  dbArrayEnd : layout.dbArray.toNat+layout.total.toNat*16≤layout.dbHeap.toNat
  pointerStart : layout.input.toNat≤pointer.toNat
  pointerEnd : pointer.toNat+length.toNat≤layout.input.toNat+layout.inputLength.toNat
  pointerNoWrap : pointer.toNat+length.toNat<2^64
  lengthBound : length.toNat≤layout.inputLength.toNat

/-- The actual source initializers establish the concrete loop invariant. -/
theorem WitnessTraversalEntryPrecondition.initializes {F : Type} (layout : WitnessTraversalLayout)
    (s : PanSemStateFiniteExact 64 F) (scratch heap pointer length : BitVec 64)
    (valid : WitnessTraversalEntryPrecondition layout s scratch heap pointer length) :
    WitnessTraversalState layout (witnessTraversalEntry s pointer length) scratch heap 0 1 1 := by
  let entry := witnessTraversalEntry s pointer length
  have built : NodedbTableAt entry layout.table layout.dbHeap layout.total := by
    obtain ⟨k,sd,c,u,v,o,op,n,b,nb,cb,room,inv,ordered,extent⟩ := valid.built
    exact ⟨k,sd,c,u,v,o,op,n,b,nb,cb,room,inv.transfer rfl rfl rfl rfl,ordered.transfer rfl rfl rfl,extent⟩
  have slices : RlpSliceInputPrefix entry layout.dbArray layout.input layout.inputLength layout.total.toNat := by
    intro index inside
    obtain ⟨p,n,slice⟩ := valid.slices index inside
    exact ⟨p,n,slice.after_frame s entry layout.dbArray index p n layout.input layout.inputLength rfl rfl rfl⟩
  have localKept (key : MlS) (different : key≠ofString "top" ∧ key≠ofString "result" ∧ key≠ofString "cur_p" ∧
      key≠ofString "cur_n" ∧ key≠ofString "mode" ∧ key≠ofString "slot" ∧ key≠ofString "go") :
      entry.locals.lookup key=s.locals.lookup key := by
    simp [entry,witnessTraversalEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      Ne.symm different.1,Ne.symm different.2.1,Ne.symm different.2.2.1,Ne.symm different.2.2.2.1,
      Ne.symm different.2.2.2.2.1,Ne.symm different.2.2.2.2.2.1,Ne.symm different.2.2.2.2.2.2]
  have atTop : entry.locals.lookup (ofString "top")=some (.val (.word (0#64))) := by
    simp (config:={decide:=true}) [entry,witnessTraversalEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atMode : entry.locals.lookup (ofString "mode")=some (.val (.word (1#64))) := by
    simp (config:={decide:=true}) [entry,witnessTraversalEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atGo : entry.locals.lookup (ofString "go")=some (.val (.word (1#64))) := by
    simp [entry,witnessTraversalEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  exact {
    code := valid.code
    atDb := (localKept (ofString "db") (by decide)).trans valid.atDb
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
    built := built
    entries := valid.entries
    slices := slices
    tableAboveDatabase := valid.tableAboveDatabase
    arrayAboveDatabase := valid.arrayAboveDatabase
    dbHeapBeforeFloor := valid.dbHeapBeforeFloor
    dbArrayEnd := valid.dbArrayEnd
    atTop := atTop
    atMode := atMode
    atGo := atGo
    stack := .nil
    scratchChain := .nil
    modes := Or.inr (Or.inl rfl)
    goBits := Or.inr rfl
    decodeInput := by
      intro _
      refine ⟨pointer,length,?_,?_,valid.pointerStart,valid.pointerEnd,valid.pointerNoWrap,valid.lengthBound⟩ <;>
        simp (config:={decide:=true}) [entry,witnessTraversalEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    resolveSelector := by intro bad;cases bad
    delivered := by intro bad;cases bad
  }
#print axioms WitnessTraversalEntryPrecondition.initializes
end InitECandidate.Runtime
