import InitECandidate.Runtime.StateInitUniformBound
import InitECandidate.Runtime.NodedbEmptySliceRetarget
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- An empty array has no source cells; use the actual live heap as its harmless
extent ghost. Nonempty arrays retain their actual source address. -/
def stateInitDatabaseArray (array count heap : BitVec 64) : BitVec 64 := if count=0 then heap else array
/-- Concrete original-memory geometry used by the actual world initializer. -/
def stateInitDatabaseLayout (table heap array count inputLength : BitVec 64) : WitnessTraversalLayout where
 table:=table
 dbHeap:=heap
 dbArray:=stateInitDatabaseArray array count heap
 total:=count
 input:=2713731432
 inputLength:=inputLength
 frame:=2701135872
 scratchUpper:=2713714688
 databaseCeiling:=2713731432
 persistentFloor:=heap.toNat
 inputLimit:=134217712

/-- Derive all initial witness-traversal obligations from concrete DB contents,
original input span, fixed workspace globals, and the actual live heap. -/
theorem state_init_database_layout_entry {F : Type} (s : PanSemStateFiniteExact 64 F)
 (table heap array count inputLength : BitVec 64)
 (code : s.code=originalRuntimeCode)
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word (2713714688#64))))
 (atFrame : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word (2701135872#64))))
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
 (aligned : heap.toNat%8=0) (capped : heap.toNat≤33806089496)
 (domain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (inputSmall : inputLength.toNat≤134217712)
 (inputEnd : 2713731432+inputLength.toNat≤heap.toNat)
 (tableAbove : 2713731432≤table.toNat)
 (arrayAbove : count.toNat=0 ∨ 2713731432≤array.toNat)
 (arrayEnd : array.toNat+count.toNat*16≤heap.toNat)
 (built : NodedbTableAt s table heap count)
 (entries : HashTableValuesIn table (NodedbSliceTargets array count) s)
 (slices : RlpSliceInputPrefix s array (2713731432#64) inputLength count.toNat) :
 WitnessTraversalEntryPrecondition (stateInitDatabaseLayout table heap array count inputLength)
  (stateInitDbContext s table) (2713714688#64) heap (2713731432#64) inputLength := by
 let chosen := stateInitDatabaseArray array count heap
 have chosenEntries : HashTableValuesIn table (NodedbSliceTargets chosen count) s := by
  by_cases empty : count=0
  · simpa only [chosen,stateInitDatabaseArray,if_pos empty] using (nodedb_empty_slice_retarget s table array heap count (2713731432#64) inputLength empty entries).1
  · simpa only [chosen,stateInitDatabaseArray,if_neg empty] using entries
 have chosenSlices : RlpSliceInputPrefix s chosen (2713731432#64) inputLength count.toNat := by
  by_cases empty : count=0
  · simpa only [chosen,stateInitDatabaseArray,if_pos empty] using (nodedb_empty_slice_retarget s table array heap count (2713731432#64) inputLength empty entries).2
  · simpa only [chosen,stateInitDatabaseArray,if_neg empty] using slices
 have chosenAbove : 2713731432≤chosen.toNat := by
  by_cases empty : count=0
  · simp only [chosen,stateInitDatabaseArray,if_pos empty];omega
  · simp only [chosen,stateInitDatabaseArray,if_neg empty]
    rcases arrayAbove with zero|above
    · exact False.elim (empty (BitVec.eq_of_toNat_eq (by simpa using zero)))
    · exact above
 have chosenEnd : chosen.toNat+count.toNat*16≤heap.toNat := by
  by_cases empty : count=0
  · simp [chosen,stateInitDatabaseArray,empty]
  · simpa only [chosen,stateInitDatabaseArray,if_neg empty] using arrayEnd
 exact {
  code:=code
  atDb:=by simp [stateInitDatabaseLayout,stateInitDbContext,HolFiniteMapExact.lookup_update,FUPDATE]
  atScratch:=atScratch
  atFrame:=atFrame
  atHeap:=atHeap
  framePositive:=by simp only [stateInitDatabaseLayout];decide
  scratchLower:=by simp only [stateInitDatabaseLayout];decide
  scratchBound:=by simp only [stateInitDatabaseLayout];decide
  scratchAligned:=by decide
  scratchBeforeDatabase:=by simp only [stateInitDatabaseLayout];decide
  databaseBeforeFloor:=by change 2713731432≤heap.toNat;omega
  floorBeforeHeap:=Nat.le_refl _
  heapBound:=capped
  heapAligned:=aligned
  inputRange:=by change 2713731432+inputLength.toNat<2^64;omega
  inputBound:=inputSmall
  inputLimitBound:=Nat.le_refl _
  inputBeforeFrame:=Or.inr (by simp only [stateInitDatabaseLayout];decide)
  inputBeforeFloor:=inputEnd
  scratchArena:=by intro address lo hi;exact domain address (by change address.toNat<2713714688 at hi;omega)
  heapArena:=by intro address lo hi;exact domain address hi
  built:=by
   obtain ⟨k,sd,c,u,v,o,op,n,b,nb,cb,room,inv,ordered,extent⟩:=built
   exact ⟨k,sd,c,u,v,o,op,n,b,nb,cb,room,inv.transfer rfl rfl rfl rfl,ordered.transfer rfl rfl rfl,extent⟩
  entries:=chosenEntries
  slices:=by
   intro index inside
   obtain ⟨p,n,slice⟩:=chosenSlices index inside
   exact ⟨p,n,slice.after_frame s (stateInitDbContext s table) chosen index p n 2713731432 inputLength rfl rfl rfl⟩
  tableAboveDatabase:=tableAbove
  arrayAboveDatabase:=chosenAbove
  dbHeapBeforeFloor:=Nat.le_refl _
  dbArrayEnd:=chosenEnd
  pointerStart:=Nat.le_refl _
  pointerEnd:=Nat.le_refl _
  pointerNoWrap:=by change 2713731432+inputLength.toNat<2^64;omega
  lengthBound:=Nat.le_refl _
 }
#print axioms state_init_database_layout_entry
end InitECandidate.Runtime
