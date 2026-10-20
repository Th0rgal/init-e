import InitECandidate.Runtime.MptInsertLeafAssignmentWorld
import InitECandidate.Runtime.MptInsertLeafDispatchBound
import InitECandidate.Runtime.TriePathBufferSlice
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual leaf arm in the outer insertion loop assigns a live result
and preserves the complete allocated world. Its sliced key argument earns its
path buffer and short length from the original input and current level. -/
theorem mpt_insert_leaf_dispatch_normal_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier node key length level value valueLength : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (keyPath : TriePathBuffer s live size key length frontier) (short : length.toNat≤18)
 (nodeLive : node∈live) (nonExt : node∉extensions) (nonBranch : node∉branches)
 (inside : level.toNat≤length.toNat)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atLevel : s.locals.lookup (ofString "level")=some (.val (.word level)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word value)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 145≤s.clock)
 (run : evaluateHOLFiniteState s mptInsertLeafDispatch=(none,post)) :
 ∃root : BitVec 64,∃larger newExtensions newBranches : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 post.locals.lookup (ofString "r")=some (.val (.word root)) ∧root∈larger ∧live⊆larger ∧extensions⊆newExtensions ∧branches⊆newBranches ∧
 AllocatedTrieWorld post larger newExtensions newBranches newSize finish ∧
 TrieNodeKinds post larger newExtensions newBranches ∧
 TrieNodePaths post larger newExtensions newBranches newSize finish ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer post larger newSize nib len finish) ∧
 (∀other : MlS,other≠ofString "r"→post.locals.lookup other=s.locals.lookup other) := by
 rw [source_mptInsert_leaf_dispatch] at run
 have remainder : (length-level).toNat≤18 := by
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr inside)]
  omega
 apply mpt_insert_leaf_assignment_world s post live extensions branches size (ofString "r") _
  frontier node (key+level) (length-level) value valueLength world kinds paths (keyPath.suffix inside)
  remainder nodeLive nonExt nonBranch _ fullDomain code budget run
 simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atNode,atKey,atLength,atLevel,atValue,atValueLength,
  wordOpHOL,wordOp,valueIsWord,valueWord]

#print axioms mpt_insert_leaf_dispatch_normal_world
end InitECandidate.Runtime
