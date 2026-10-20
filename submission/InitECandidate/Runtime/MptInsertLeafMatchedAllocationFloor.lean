import InitECandidate.Runtime.TrieAllocationFloorFrame
import InitECandidate.Runtime.MptInsertPayloadPathsWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The two real equal-key leaf payload stores preserve the allocation boundary of every record and stored path. -/
theorem evaluate_mpt_insert_leaf_matched_allocation_floor {F : Type} (s : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (frontier node value length : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (floor : Nat) (lower : TrieAllocationFloor s live branches floor)
 (member : node∈live) (tag : s.memory node=.word (1#64))
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word value)))
 (atLength : s.locals.lookup (ofString "vlen")=some (.val (.word length)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address) :
 ∃post,evaluateHOLFiniteState s mptInsertLeafMatched=(some (.returned (.val (.word node))),post) ∧
 TrieAllocationFloor post live branches floor := by
 obtain ⟨notExtension,notBranch⟩:=kinds.leaf_separate node tag
 have capacity:=paths.leafCapacity node member notExtension notBranch
 obtain ⟨post,run,_,_,_,_,_,_,frame⟩:=evaluate_mpt_insert_leaf_matched_world
  s live extensions branches size frontier node value length world kinds member capacity tag
  atNode atValue atLength fullDomain
 refine ⟨post,run,?_⟩
 apply lower.after_record_fields paths world node member [48,56]
 · intro field included
   simp only [List.mem_cons,List.not_mem_nil,or_false] at included
   rcases included with rfl|rfl <;>omega
 · right;intro field included
   simp only [List.mem_cons,List.not_mem_nil,or_false] at included
   rcases included with rfl|rfl <;>decide
 · intro watched separate
   exact frame watched (separate 48 (by simp)) (separate 56 (by simp))

#print axioms evaluate_mpt_insert_leaf_matched_allocation_floor
end InitECandidate.Runtime
