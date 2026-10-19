import InitECandidate.Runtime.WitnessUnwindModeMemoryFrame
import InitECandidate.Runtime.WitnessUnwindDatabaseLocal
import InitECandidate.Runtime.NodedbContentsBetweenFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem witness_unwind_branch_mode_database_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array pointer length scratch frame top heap index hash : BitVec 64) (ceiling inputLimit : Nat)
    (arrayReadable : s.memaddrs (top+24#64)) (arrayCell : s.memory (top+24#64) = .word array)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (result : BitVec 64)
    (atResult : s.locals.lookup (ofString "result") = some (.val (.word result)))
    (recordBeforeTable : top.toNat+88 ≤ array.toNat)
    (tableBeforeBranch : array.toNat+272 ≤ heap.toNat)
    (branchReadable : s.memaddrs (top+16#64)) (branchCell : s.memory (top+16#64)=.word heap)
    (indexReadable : s.memaddrs (top+32#64)) (indexCell : s.memory (top+32#64)=.word index)
    (indexBound : index.toNat < 16)
    (heapBound : heap.toNat ≤ 33806089496)
    (slice : RlpSliceEntry s array 16 pointer length)
    (inputRange : pointer.toNat+length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit+9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (hashReadable : s.memaddrs (top+80#64)) (hashCell : s.memory (top+80#64)=.word hash)
    (stageReadable : s.memaddrs (top+8#64)) (stageCell : s.memory (top+8#64)=.word (2#64))
    (resultAfterTable : result=0 ∨ array.toNat+272 ≤ result.toNat)
    (resultBound : result.toNat ≤ 33806089496)
    (budget : witnessBranchFinishCost length.toNat ≤ s.clock)
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
    (ceilingOrdered : ceiling≤databaseCeiling)
    (floorBeforeBranch : persistentFloor≤heap.toNat)
    (run : evaluateHOLFiniteState s decodeWitnessNodeUnwindMode=(none,post)) :
    NodedbTableAt post table dbHeap dbTotal ∧
    HashTableValuesIn table (NodedbSliceTargets dbArray dbTotal) post ∧
    RlpSliceInputPrefix post dbArray globalInput globalLength dbTotal.toNat ∧
    post.memaddrs=s.memaddrs ∧ post.be=s.be ∧ post.code=s.code ∧
    post.locals.lookup (ofString "db")=some (.val (.word table)) ∧
    post.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)) ∧
    post.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)) ∧
    post.globals.lookup (ofString "heap_ptr")=s.globals.lookup (ofString "heap_ptr") ∧
    ∀ watched : BitVec 64, databaseCeiling≤watched.toNat → watched.toNat<dbHeap.toNat →
      post.memory watched=s.memory watched := by
  obtain ⟨scratchPost,framePost,heapPost,memory⟩ := witness_unwind_branch_mode_memory_frame s post
    array pointer length scratch frame top heap index hash ceiling inputLimit arrayReadable arrayCell atTop result atResult
    recordBeforeTable tableBeforeBranch branchReadable branchCell indexReadable indexCell indexBound heapBound
    slice inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    hashReadable hashCell stageReadable stageCell resultAfterTable resultBound budget nonzero run
  have metadata := evaluateHOLFiniteState_metadata s decodeWitnessNodeUnwindMode
  rw [run] at metadata
  have topNat (offset : Nat) (small : offset<88) : (top+BitVec.ofNat 64 offset).toNat=top.toNat+offset := by
    rw [BitVec.toNat_add,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : offset<2^64),Nat.mod_eq_of_lt (by omega : top.toNat+offset<2^64)]
  have resultNat : (result+(24 : BitVec 64)).toNat=result.toNat+24 := by
    rw [BitVec.toNat_add]
    change (result.toNat+24)%2^64=result.toNat+24
    exact Nat.mod_eq_of_lt (by omega)
  have dbMemory (watched : BitVec 64) (above : databaseCeiling≤watched.toNat) (below : watched.toNat<dbHeap.toNat) :
      post.memory watched=s.memory watched := by
    apply memory watched (by omega) (by omega)
    · intro same
      have equal:=congrArg BitVec.toNat same
      change watched.toNat=(top+32#64).toNat at equal
      rw [topNat 32 (by decide)] at equal
      omega
    · intro same
      have equal:=congrArg BitVec.toNat same
      change watched.toNat=(top+40#64).toNat at equal
      rw [topNat 40 (by decide)] at equal
      omega
    · rcases resultAfterFloor with zero | lower
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
    (witness_unwind_db_normal_kept s post run).trans atDb,scratchPost,framePost,heapPost,dbMemory⟩

#print axioms witness_unwind_branch_mode_database_frame
end InitECandidate.Runtime
