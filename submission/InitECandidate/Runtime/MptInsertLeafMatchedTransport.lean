import InitECandidate.Runtime.TriePathBufferFieldsFrame
import InitECandidate.Runtime.MptInsertPayloadPathsWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The two real payload stores in an equal-key leaf preserve the allocated
world, stored node paths, and every other separated input path buffer. -/
theorem evaluate_mpt_insert_leaf_matched_transport_world {F : Type} (s : PanSemStateFiniteExact 64 F)
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
 TrieNodePaths post live extensions branches size frontier ∧post.globals=s.globals ∧
 (∀key len,TriePathBuffer s live size key len frontier→TriePathBuffer post live size key len frontier) := by
 obtain ⟨post,run,worldOut,kindsOut,pathsOut,globals⟩:=evaluate_mpt_insert_leaf_matched_paths_world
  s live extensions branches size frontier node value length world kinds paths member tag
  atNode atValue atLength fullDomain
 obtain ⟨notExtension,notBranch⟩:=kinds.leaf_separate node tag
 have capacity:=paths.leafCapacity node member notExtension notBranch
 obtain ⟨other,otherRun,_,_,_,_,_,_,frame⟩:=evaluate_mpt_insert_leaf_matched_world
  s live extensions branches size frontier node value length world kinds member capacity tag
  atNode atValue atLength fullDomain
 have same : other=post:=(Prod.mk.inj (otherRun.symm.trans run)).2
 subst other
 have metadata:=evaluateHOLFiniteState_metadata s mptInsertLeafMatched
 rw [run] at metadata
 refine ⟨post,run,worldOut,kindsOut,pathsOut,globals,?_⟩
 intro key len path
 apply path.after_record_fields world node member [48,56]
 · intro field included
   simp only [List.mem_cons,List.not_mem_nil,or_false] at included
   rcases included with rfl|rfl <;>omega
 · intro watched separate
   exact frame watched (separate 48 (by simp)) (separate 56 (by simp))
 · exact metadata.2.1
 · exact metadata.2.2.1

#print axioms TriePathBuffer.after_record_fields
#print axioms evaluate_mpt_insert_leaf_matched_transport_world
end InitECandidate.Runtime
