import InitECandidate.Runtime.WitnessDecodeModeHeapFrame
import InitECandidate.Runtime.NodedbContentsBetweenFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem witness_decode_mode_normal_database_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (table pointer length scratch frame array previous : BitVec 64) (ceiling inputLimit : Nat)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word previous)))
    (atTable : s.locals.lookup (ofString "db") = some (.val (.word table)))
    (atPointer : s.locals.lookup (ofString "cur_p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "cur_n") = some (.val (.word length)))
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : decodeStepBodyCost inputLimit + 1 ≤ s.clock)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (aligned : array.toNat%8=0) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (arrayAbove : ceiling ≤ array.toNat) (limitCap : inputLimit ≤ 134217712)
    (dbHeap dbArray dbTotal globalInput globalLength : BitVec 64)
    (built : NodedbTableAt s table dbHeap dbTotal)
    (entries : HashTableValuesIn table (NodedbSliceTargets dbArray dbTotal) s)
    (slices : RlpSliceInputPrefix s dbArray globalInput globalLength dbTotal.toNat)
    (tableAbove : ceiling ≤ table.toNat) (dbArrayAbove : ceiling ≤ dbArray.toNat)
    (tableEnd : dbHeap.toNat ≤ array.toNat)
    (dbArrayEnd : dbArray.toNat+dbTotal.toNat*16 ≤ array.toNat)
    (run : evaluateHOLFiniteState s decodeWitnessNodeDecodeMode = (none,post)) :
    NodedbTableAt post table dbHeap dbTotal ∧
      HashTableValuesIn table (NodedbSliceTargets dbArray dbTotal) post ∧
      RlpSliceInputPrefix post dbArray globalInput globalLength dbTotal.toNat ∧
      post.memaddrs=s.memaddrs ∧ post.be=s.be ∧ post.code=s.code ∧
      (∀ oldRecord : BitVec 64, ceiling ≤ oldRecord.toNat → oldRecord.toNat+88 ≤ array.toNat →
        ∀ offset : Nat, offset < 88 → post.memory (oldRecord+BitVec.ofNat 64 offset)=s.memory (oldRecord+BitVec.ofNat 64 offset)) ∧
      ∃ nextHeap : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
        array.toNat ≤ nextHeap.toNat ∧ nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat%8=0 := by
  obtain ⟨nextHeap,heapPost,growth,capped,finishAligned,memory⟩ := witness_decode_mode_normal_heap_frame s post
    table pointer length scratch frame array previous ceiling inputLimit atTop atTable atPointer atLength
    inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    budget heap arrayBound aligned countLimit heapArena inputBeforeFrame inputBeforeArray arrayAbove limitCap run
  have metadata := evaluateHOLFiniteState_metadata s decodeWitnessNodeDecodeMode
  rw [run] at metadata
  obtain ⟨builtPost,entriesPost,slicesPost⟩ := nodedb_contents_after_between_frame s post table dbHeap dbArray dbTotal
    globalInput globalLength array ceiling built entries slices tableAbove dbArrayAbove tableEnd dbArrayEnd
    metadata.2.1 metadata.2.2.1 metadata.1 memory
  refine ⟨builtPost,entriesPost,slicesPost,metadata.2.1,metadata.2.2.1,metadata.1,?_,
    nextHeap,heapPost,growth,capped,finishAligned⟩
  intro oldRecord recordAbove recordBefore offset inside
  have offsetNat : (BitVec.ofNat 64 offset).toNat=offset := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have addressNat : (oldRecord+BitVec.ofNat 64 offset).toNat=oldRecord.toNat+offset := by
    rw [BitVec.toNat_add,offsetNat]
    exact Nat.mod_eq_of_lt (by have limit := array.isLt; omega)
  exact memory _ (by rw [addressNat]; omega) (by rw [addressNat]; omega)

#print axioms witness_decode_mode_normal_database_frame
end InitECandidate.Runtime
