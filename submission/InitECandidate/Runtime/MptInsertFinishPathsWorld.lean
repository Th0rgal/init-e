import InitECandidate.Runtime.MptInsertCommitPathsWorld
import InitECandidate.Runtime.MptInsertAdvanceFrame
import InitECandidate.Runtime.MptInsertFinish
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete normal finish: commit followed by the actual traversal assignments.
No idempotent-backlink assumption is needed; a new live root is allowed. -/
theorem mpt_insert_finish_normal_paths_world {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
    (frontier : BitVec 64)
    (world : AllocatedTrieWorld state live extensions branches size frontier)
    (kinds : TrieNodeKinds state live extensions branches)
    (paths : TrieNodePaths state live extensions branches size frontier)
    (slot result oldRoot : BitVec 64)
    (slotLocal : state.locals.lookup (ofString "slot") = some (.val (.word slot)))
    (resultLocal : state.locals.lookup (ofString "r") = some (.val (.word result)))
    (rootLocal : state.locals.lookup (ofString "result") = some (.val (.word oldRoot)))
    (resultValid : result = 0 ∨ result ∈ live) (rootValid : oldRoot = 0 ∨ oldRoot ∈ live)
    (typedSlot : slot ≠ 0 → TrieChildSlot state extensions branches slot)
    (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→state.memaddrs address)
    (run : evaluateHOLFiniteState state mptInsertFinish=(none,post)) :
    ∃root : BitVec 64,
      AllocatedTrieWorld post live extensions branches size frontier ∧
      TrieNodeKinds post live extensions branches ∧TrieNodePaths post live extensions branches size frontier ∧
      post.locals.lookup (ofString "result")=some (.val (.word root)) ∧(root=0 ∨root∈live) ∧
      (∀key len,TriePathBuffer state live size key len frontier→TriePathBuffer post live size key len frontier) := by
 rw [source_mptInsert_finish] at run
 obtain ⟨middle,commit,advance⟩:=seq_normal_parts run
 obtain ⟨actual,root,evaluated,worldOut,kindsOut,pathsOut,_,rootAt,rootValid,transport⟩:=
  evaluate_mpt_insert_commit_paths_world state live extensions branches size frontier world kinds paths
   slot result oldRoot slotLocal resultLocal rootLocal resultValid rootValid typedSlot fullDomain
 have same : actual=middle:=(Prod.mk.inj (evaluated.symm.trans commit)).2
 subst actual
 obtain ⟨memory,globals⟩:=mpt_insert_advance_normal_frame middle post advance
 have metadata:=evaluateHOLFiniteState_metadata middle mptInsertAdvance
 rw [advance] at metadata
 have kept:=evaluate_avoidsLocal_flowing (ofString "result") mptInsertAdvance
  (by rw [source_mptInsert_advance];decide) middle
 rw [advance] at kept
 refine ⟨root,worldOut.after_memory_globals memory globals,?_,
  pathsOut.after_context memory metadata.2.1 metadata.2.2.1,(kept (Or.inl rfl)).trans rootAt,rootValid,?_⟩
 · exact kindsOut.after_kind_frame worldOut.layout.extensionLive worldOut.layout.branchLive
    (by intro node member;exact congrFun memory node)
 · intro key len path
   exact (transport key len path).after_context memory metadata.2.1 metadata.2.2.1

#print axioms mpt_insert_finish_normal_paths_world
end InitECandidate.Runtime
