import InitECandidate.Runtime.NodeNewLeafAssignmentWorld
import InitECandidate.Runtime.MptInsertNullStep
import InitECandidate.Runtime.TriePathBufferSlice
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual null-node selection creates a live leaf from the remaining
input key and transports all paths, with no future constructor callback. -/
theorem mpt_insert_new_leaf_call_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (pointer key length level value valueLength : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size pointer)
 (keyPath : TriePathBuffer s live size key length pointer) (short : length.toNat≤18)
 (inside : level.toNat≤length.toNat)
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atLevel : s.locals.lookup (ofString "level")=some (.val (.word level)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word value)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s mptInsertNewLeafCall=(none,post)) :
 post.locals.lookup (ofString "r")=some (.val (.word pointer)) ∧
 AllocatedTrieWorld post (insert pointer live) extensions branches
  (Function.update size pointer 64) (allocationEnd pointer 64) ∧
 TrieNodeKinds post (insert pointer live) extensions branches ∧
 TrieNodePaths post (insert pointer live) extensions branches
  (Function.update size pointer 64) (allocationEnd pointer 64) ∧
 (∀key len,TriePathBuffer s live size key len pointer→
  TriePathBuffer post (insert pointer live) (Function.update size pointer 64) key len (allocationEnd pointer 64)) ∧
 (∀other : MlS,other≠ofString "r"→post.locals.lookup other=s.locals.lookup other) := by
 have remainder : (length-level).toNat≤18 := by
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr inside)];omega
 unfold mptInsertNewLeafCall at run
 apply node_new_leaf_assignment_world s post live extensions branches size pointer (key+level) (length-level)
  value valueLength world kinds paths (keyPath.suffix inside) remainder (ofString "r") _ _ fullDomain code run
 simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atKey,atLength,atLevel,atValue,atValueLength,
  wordOpHOL,wordOp,valueIsWord,valueWord]

#print axioms mpt_insert_new_leaf_call_world
end InitECandidate.Runtime
