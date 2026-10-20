import InitECandidate.Runtime.MptInsertLeafEqualWorld
import InitECandidate.Runtime.MptInsertBranchValueWorld
import InitECandidate.Runtime.TrieNodePathsFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual equal-key terminal leaf stores preserve every stored path.
The reachable leaf capacity is obtained from the concrete node-path invariant. -/
theorem evaluate_mpt_insert_leaf_matched_paths_world {F : Type} (s : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (frontier node value length : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (member : node∈live) (tag : s.memory node=.word (1#64))
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word value)))
 (atLength : s.locals.lookup (ofString "vlen")=some (.val (.word length)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address) :
 ∃post,evaluateHOLFiniteState s mptInsertLeafMatched=(some (.returned (.val (.word node))),post) ∧
 AllocatedTrieWorld post live extensions branches size frontier ∧TrieNodeKinds post live extensions branches ∧
 TrieNodePaths post live extensions branches size frontier ∧post.globals=s.globals := by
 obtain ⟨notExtension,notBranch⟩:=kinds.leaf_separate node tag
 have capacity:=paths.leafCapacity node member notExtension notBranch
 obtain ⟨post,run,worldOut,kindsOut,_,_,globals,_,frame⟩:=evaluate_mpt_insert_leaf_matched_world s live extensions branches size frontier node value length world kinds member capacity tag atNode atValue atLength fullDomain
 have metadata:=evaluateHOLFiniteState_metadata s mptInsertLeafMatched
 rw [run] at metadata
 refine ⟨post,run,worldOut,kindsOut,?_,globals⟩
 apply paths.after_record_fields world node member [48,56]
 · intro field included;simp only [List.mem_cons,List.not_mem_nil,or_false] at included
   rcases included with rfl|rfl <;>omega
 · right;intro field included;simp only [List.mem_cons,List.not_mem_nil,or_false] at included
   rcases included with rfl|rfl <;>decide
 · intro watched separate
   exact frame watched (separate 48 (by simp)) (separate 56 (by simp))
 · exact metadata.2.1
 · exact metadata.2.2.1

/-- The actual terminal branch payload update also keeps all stored paths;
its two value words lie beyond every child slot and every segment header. -/
theorem evaluate_mpt_insert_branch_value_paths_world {F : Type} (s : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (frontier node value length oldResult : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier) (member : node∈branches)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word value)))
 (atLength : s.locals.lookup (ofString "vlen")=some (.val (.word length)))
 (atResult : s.locals.lookup (ofString "r")=some (.val (.word oldResult)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address) :
 ∃post,evaluateHOLFiniteState s mptInsertBranchValue=(none,post) ∧
 AllocatedTrieWorld post live extensions branches size frontier ∧TrieNodeKinds post live extensions branches ∧
 TrieNodePaths post live extensions branches size frontier ∧post.locals.lookup (ofString "r")=some (.val (.word node)) := by
 obtain ⟨post,run,worldOut,kindsOut,_,result,_,_,_,frame⟩:=evaluate_mpt_insert_branch_value_world s live extensions branches size frontier world kinds node value length oldResult member atNode atValue atLength atResult fullDomain
 have metadata:=evaluateHOLFiniteState_metadata s mptInsertBranchValue
 rw [run] at metadata
 refine ⟨post,run,worldOut,kindsOut,?_,result⟩
 apply paths.after_record_fields world node (world.layout.branchLive member) [160,168]
 · intro field included;simp only [List.mem_cons,List.not_mem_nil,or_false] at included
   have capacity:=world.layout.branchSize node member
   rcases included with rfl|rfl <;>omega
 · exact Or.inl member
 · intro watched separate
   exact frame watched (separate 160 (by simp)) (separate 168 (by simp))
 · exact metadata.2.1
 · exact metadata.2.2.1

#print axioms evaluate_mpt_insert_leaf_matched_paths_world
#print axioms evaluate_mpt_insert_branch_value_paths_world
end InitECandidate.Runtime
