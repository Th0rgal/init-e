import InitECandidate.Runtime.WitnessResolveModeHeapFrame
import InitECandidate.Runtime.NodedbContentsBetweenFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem witness_resolve_mode_normal_database_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame table dbHeap array total input inputLength childArray slot top heapPointer : BitVec 64)
    (ceiling inputLimit : Nat)
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (heapAligned : heapPointer.toNat%8=0)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (arrayReadable : s.memaddrs (top+24#64)) (arrayCell : s.memory (top+24#64) = .word childArray)
    (atSlot : s.locals.lookup (ofString "slot") = some (.val (.word slot)))
    (slice : RlpSliceEntry s childArray slot pointer length)
    (atTable : s.locals.lookup (ofString "db") = some (.val (.word table)))
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (built : NodedbTableAt s table dbHeap total)
    (entries : HashTableValuesIn table (NodedbSliceTargets array total) s)
    (slices : RlpSliceInputPrefix s array input inputLength total.toNat)
    (tableAbove : ceiling ≤ table.toNat) (arrayAbove : ceiling ≤ array.toNat)
    (arrayEnd : array.toNat + total.toNat*16 ≤ dbHeap.toNat)
    (spanLo : input.toNat ≤ pointer.toNat)
    (spanHi : pointer.toNat+length.toNat ≤ input.toNat+inputLength.toNat)
    (spanSize : length.toNat ≤ inputLength.toNat)
    (budget : resolveStepBodyCost length.toNat + 1 ≤ s.clock)
    (databaseCeiling : Nat) (ceilingOrdered : ceiling ≤ databaseCeiling)
    (topAbove : ceiling ≤ top.toNat) (recordBeforeDatabase : top.toNat+88 ≤ databaseCeiling)
    (databaseBeforeHeap : databaseCeiling ≤ heapPointer.toNat)
    (tableAboveDatabase : databaseCeiling ≤ table.toNat) (arrayAboveDatabase : databaseCeiling ≤ array.toNat)
    (dbHeapBeforeHeap : dbHeap.toNat ≤ heapPointer.toNat)
    (run : evaluateHOLFiniteState s decodeWitnessNodeResolveMode = (none,post)) :
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
      NodedbTableAt post table dbHeap total ∧
      HashTableValuesIn table (NodedbSliceTargets array total) post ∧
      RlpSliceInputPrefix post array input inputLength total.toNat ∧
      post.memaddrs=s.memaddrs ∧ post.be=s.be ∧ post.code=s.code ∧
      (∀ offset : Nat, offset < 88 → offset ≠ 80 →
        post.memory (top+BitVec.ofNat 64 offset)=s.memory (top+BitVec.ofNat 64 offset)) ∧
      ∃ nextHeap : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
        heapPointer.toNat ≤ nextHeap.toNat ∧ nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat%8=0 ∧
        ∀ watched : BitVec 64, ceiling ≤ watched.toNat → watched.toNat < heapPointer.toNat → watched ≠ top+80 →
          post.memory watched=s.memory watched := by
  obtain ⟨scratchPost,framePost,nextHeap,heapPost,growth,capped,aligned,memory⟩ := witness_resolve_mode_normal_heap_frame
    s post pointer length scratch frame table dbHeap array total input inputLength childArray slot top heapPointer ceiling inputLimit
    atHeap heapBound heapAligned atTop arrayReadable arrayCell atSlot slice atTable inputRange lengthBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena built entries slices tableAbove arrayAbove
    arrayEnd spanLo spanHi spanSize budget run
  have metadata := evaluateHOLFiniteState_metadata s decodeWitnessNodeResolveMode
  rw [run] at metadata
  have hashNat : (top+(80 : BitVec 64)).toNat=top.toNat+80 := by
    rw [BitVec.toNat_add]
    change (top.toNat+80)%2^64=top.toNat+80
    exact Nat.mod_eq_of_lt (by have limit := heapPointer.isLt; omega)
  have dbMemory : ∀ watched : BitVec 64, databaseCeiling ≤ watched.toNat → watched.toNat < heapPointer.toNat →
      post.memory watched=s.memory watched := by
    intro watched above before
    apply memory watched (by omega) before
    intro same
    have equal := congrArg BitVec.toNat same
    rw [hashNat] at equal
    omega
  obtain ⟨builtPost,entriesPost,slicesPost⟩ := nodedb_contents_after_between_frame s post table dbHeap array total input inputLength
    heapPointer databaseCeiling built entries slices tableAboveDatabase arrayAboveDatabase dbHeapBeforeHeap
    (arrayEnd.trans dbHeapBeforeHeap) metadata.2.1 metadata.2.2.1 metadata.1 dbMemory
  refine ⟨scratchPost,framePost,builtPost,entriesPost,slicesPost,metadata.2.1,metadata.2.2.1,metadata.1,?_,
    nextHeap,heapPost,growth,capped,aligned,memory⟩
  intro offset inside different
  have offsetNat : (BitVec.ofNat 64 offset).toNat=offset := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have addressNat : (top+BitVec.ofNat 64 offset).toNat=top.toNat+offset := by
    rw [BitVec.toNat_add,offsetNat]
    exact Nat.mod_eq_of_lt (by have limit := heapPointer.isLt; omega)
  apply memory _ (by rw [addressNat]; omega) (by rw [addressNat]; omega)
  intro same
  have equal := congrArg BitVec.toNat same
  rw [addressNat,hashNat] at equal
  omega

#print axioms witness_resolve_mode_normal_database_frame
end InitECandidate.Runtime
