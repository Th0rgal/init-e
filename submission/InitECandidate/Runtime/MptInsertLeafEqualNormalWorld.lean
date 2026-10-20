import InitECandidate.Runtime.MptInsertPayloadPathsWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual equal-key return guard can fall through only by taking skip.
Its store arm is terminal, as established by the real allocated leaf stores;
no callee result or arbitrary memory frame is a premise. -/
theorem mpt_insert_leaf_equal_normal_identity {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (frontier node value length : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (member : node∈live) (tag : s.memory node=.word (1#64))
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word value)))
 (atLength : s.locals.lookup (ofString "vlen")=some (.val (.word length)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (run : evaluateHOLFiniteState s mptInsertLeafEqualReturn=(none,post)) :
 post=s := by
 rw [source_mpt_insert_leaf_equal_return,evaluateHOLFiniteState_ite] at run
 split at run
 · split at run
   · rw [evaluateHOLFiniteState_skip] at run
     exact (Prod.mk.inj run).2.symm
   · obtain ⟨matched,matchedRun,rest⟩:=evaluate_mpt_insert_leaf_matched_paths_world
      s live extensions branches size frontier node value length world kinds paths member tag
      atNode atValue atLength fullDomain
     rw [matchedRun] at run
     cases run
 · simp at run

#print axioms mpt_insert_leaf_equal_normal_identity
end InitECandidate.Runtime
