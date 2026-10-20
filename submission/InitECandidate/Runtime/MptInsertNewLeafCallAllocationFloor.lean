import InitECandidate.Runtime.NodeNewLeafAssignmentAllocationFloor
import InitECandidate.Runtime.TrieAllocationFloorFrame
import InitECandidate.Runtime.MptInsertNullStep
import InitECandidate.Runtime.TriePathBufferSlice
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual null-node selection creates a live leaf from the remaining
input key and transports all paths, with no future constructor callback. -/
theorem mpt_insert_new_leaf_call_allocation_floor {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (pointer key length level value valueLength : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size pointer)
 (keyPath : TriePathBuffer s live size key length pointer) (short : length.toNat≤18)
 (floor : Nat) (lower : TrieAllocationFloor s live branches floor)
 (heapAbove : floor≤pointer.toNat) (keyAbove : floor≤key.toNat)
 (inside : level.toNat≤length.toNat)
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atLevel : s.locals.lookup (ofString "level")=some (.val (.word level)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word value)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s mptInsertNewLeafCall=(none,post)) :
 TrieAllocationFloor post (insert pointer live) branches floor := by
 have remainder : (length-level).toNat≤18 := by
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr inside)];omega
 unfold mptInsertNewLeafCall at run
 apply node_new_leaf_assignment_allocation_floor s post live extensions branches size pointer (key+level) (length-level)
  value valueLength world kinds paths (keyPath.suffix inside) remainder floor lower heapAbove ?_ (ofString "r") _ ?_ fullDomain code run
 · have extent : key.toNat+length.toNat<2^64:=by have:=keyPath.extent;have:=pointer.isLt;omega
   simpa using trie_path_slice_above_floor key length floor level.toNat keyAbove extent inside
 ·
   simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atKey,atLength,atLevel,atValue,atValueLength,
  wordOpHOL,wordOp,valueIsWord,valueWord]

#print axioms mpt_insert_new_leaf_call_allocation_floor
end InitECandidate.Runtime
