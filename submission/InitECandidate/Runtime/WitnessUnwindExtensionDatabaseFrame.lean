import InitECandidate.Runtime.WitnessUnwindModeMemoryFrame
import InitECandidate.Runtime.WitnessUnwindDatabaseLocal
import InitECandidate.Runtime.NodedbContentsBetweenFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem witness_unwind_extension_mode_database_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (top result hash heap : BitVec 64)
    (atTop : s.locals.lookup (ofString "top")=some (.val (.word top)))
    (atResult : s.locals.lookup (ofString "result")=some (.val (.word result)))
    (hashReadable : s.memaddrs (top+80#64)) (hashCell : s.memory (top+80#64)=.word hash)
    (stageReadable : s.memaddrs (top+8#64)) (stageCell : s.memory (top+8#64)=.word (1#64))
    (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496)
    (topBound : top.toNat+88 ≤ 33806089496)
    (resultAfterRecord : result=0 ∨ top.toNat+88 ≤ result.toNat)
    (resultBound : result.toNat ≤ 33806089496)
    (code : s.code=originalRuntimeCode)
    (nonzero : top ≠ 0)
    (table dbHeap dbArray dbTotal globalInput globalLength : BitVec 64)
    (databaseCeiling persistentFloor : Nat)
    (atDb : s.locals.lookup (ofString "db")=some (.val (.word table)))
    (built : NodedbTableAt s table dbHeap dbTotal)
    (entries : HashTableValuesIn table (NodedbSliceTargets dbArray dbTotal) s)
    (slices : RlpSliceInputPrefix s dbArray globalInput globalLength dbTotal.toNat)
    (tableAboveDatabase : databaseCeiling≤table.toNat)
    (arrayAboveDatabase : databaseCeiling≤dbArray.toNat)
    (dbHeapBeforeFloor : dbHeap.toNat≤persistentFloor)
    (dbArrayEnd : dbArray.toNat+dbTotal.toNat*16≤dbHeap.toNat)
    (recordBeforeDatabase : top.toNat+88≤databaseCeiling)
    (resultAfterFloor : result=0 ∨ persistentFloor≤result.toNat)
    (floorBeforeHeap : persistentFloor≤heap.toNat)
    (run : evaluateHOLFiniteState s decodeWitnessNodeUnwindMode=(none,post)) :
    NodedbTableAt post table dbHeap dbTotal ∧
    HashTableValuesIn table (NodedbSliceTargets dbArray dbTotal) post ∧
    RlpSliceInputPrefix post dbArray globalInput globalLength dbTotal.toNat ∧
    post.memaddrs=s.memaddrs ∧ post.be=s.be ∧ post.code=s.code ∧
    post.locals.lookup (ofString "db")=some (.val (.word table)) ∧
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word (allocationEnd heap 56))) ∧
    heap.toNat≤(allocationEnd heap 56).toNat ∧ (allocationEnd heap 56).toNat≤33806089496 ∧
    (allocationEnd heap 56).toNat%8=0 ∧
    post.globals.lookup (ofString "scratch_ptr")=s.globals.lookup (ofString "scratch_ptr") ∧
    post.globals.lookup (ofString "frame_mem_ptr")=s.globals.lookup (ofString "frame_mem_ptr") ∧
    ∀ watched : BitVec 64, databaseCeiling≤watched.toNat → watched.toNat<dbHeap.toNat →
      post.memory watched=s.memory watched := by
  obtain ⟨heapPost,mono,cap,aligned,scratchPost,framePost,memory⟩ := witness_unwind_extension_mode_heap_frame s post
    top result hash heap atTop atResult hashReadable hashCell stageReadable stageCell atHeap heapBound topBound
    resultAfterRecord resultBound code nonzero run
  have metadata := evaluateHOLFiniteState_metadata s decodeWitnessNodeUnwindMode
  rw [run] at metadata
  have resultNat : (result+(24 : BitVec 64)).toNat=result.toNat+24 := by
    rw [BitVec.toNat_add]
    change (result.toNat+24)%2^64=result.toNat+24
    exact Nat.mod_eq_of_lt (by omega)
  have dbMemory (watched : BitVec 64) (above : databaseCeiling≤watched.toNat) (below : watched.toNat<dbHeap.toNat) :
      post.memory watched=s.memory watched := by
    apply memory watched (by omega)
    rcases resultAfterFloor with zero | lower
    · exact Or.inl zero
    · apply Or.inr
      intro same
      have equal:=congrArg BitVec.toNat same
      rw [resultNat] at equal
      omega
  obtain ⟨builtPost,entriesPost,slicesPost⟩ := nodedb_contents_after_between_frame s post table dbHeap dbArray dbTotal
    globalInput globalLength dbHeap databaseCeiling built entries slices tableAboveDatabase arrayAboveDatabase (by rfl) dbArrayEnd
    metadata.2.1 metadata.2.2.1 metadata.1 dbMemory
  exact ⟨builtPost,entriesPost,slicesPost,metadata.2.1,metadata.2.2.1,metadata.1,
    (witness_unwind_db_normal_kept s post run).trans atDb,heapPost,mono,cap,aligned,scratchPost,framePost,dbMemory⟩

#print axioms witness_unwind_extension_mode_database_frame
end InitECandidate.Runtime
