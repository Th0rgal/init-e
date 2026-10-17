import InitECandidate.Runtime.MptInsertAdvance
import InitECandidate.Runtime.MptInsertCommitFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def mptInsertFinish : ProgHOL 64 :=
  match mptInsertLoopStep with
  | .dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.seq _ (.seq _ finish))))) => finish
  | _ => .skip

theorem source_mptInsert_finish : mptInsertFinish = .seq mptInsertCommit mptInsertAdvance := by
  simp only [mptInsertFinish,mptInsertCommit,mptInsertAdvance,mptInsertLoopStep,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original iteration suffix commits a live result and installs the
prepared next traversal state, preserving registry and root validity. -/
theorem evaluate_mptInsert_finish {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
    (layout : TrieNodeLayout live extensions branches size)
    (registry : TrieWalkRegistry live extensions branches state)
    (node slot level result oldRoot nextNode nextSlot nextLevel : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (slotLocal : state.locals.lookup (ofString "slot") = some (.val (.word slot)))
    (levelLocal : state.locals.lookup (ofString "level") = some (.val (.word level)))
    (resultLocal : state.locals.lookup (ofString "r") = some (.val (.word result)))
    (oldRootLocal : state.locals.lookup (ofString "result") = some (.val (.word oldRoot)))
    (nextNodeLocal : state.locals.lookup (ofString "next_node") = some (.val (.word nextNode)))
    (nextSlotLocal : state.locals.lookup (ofString "next_slot") = some (.val (.word nextSlot)))
    (nextLevelLocal : state.locals.lookup (ofString "next_level") = some (.val (.word nextLevel)))
    (resultValid : result = 0 ∨ result ∈ live) (rootValid : oldRoot = 0 ∨ oldRoot ∈ live)
    (childValid : nextNode = 0 ∨ nextNode ∈ live)
    (prepared : TrieChildSlot state extensions branches nextSlot)
    (typedSlot : slot ≠ 0 → TrieChildSlot state extensions branches slot)
    (domain : slot ≠ 0 → state.memaddrs slot) :
    ∃ post root, evaluateHOLFiniteState state mptInsertFinish = (none,post) ∧
      TrieWalkRegistry live extensions branches post ∧ post.clock = state.clock ∧
      post.locals.lookup (ofString "result") = some (.val (.word root)) ∧ (root = 0 ∨ root ∈ live) ∧
      post.locals.lookup (ofString "node") = some (.val (.word nextNode)) ∧ (nextNode = 0 ∨ nextNode ∈ live) ∧
      post.locals.lookup (ofString "slot") = some (.val (.word nextSlot)) ∧ TrieChildSlot post extensions branches nextSlot ∧
      post.locals.lookup (ofString "level") = some (.val (.word nextLevel)) ∧
      (∀ name, name ≠ ofString "result" → name ≠ ofString "node" → name ≠ ofString "slot" → name ≠ ofString "level" →
        post.locals.lookup name = state.locals.lookup name) := by
  obtain ⟨middle,root,commit,registered,clock,rootLocal,rootValid,slotTyped,kept⟩ :=
    evaluate_mptInsert_commit_frame state live extensions branches size layout registry nextSlot prepared
      slot result oldRoot slotLocal resultLocal oldRootLocal resultValid rootValid typedSlot domain
  obtain ⟨post,advance,atNode,atSlot,atLevel,childValid,slotValid,registry,memory,postClock,framed⟩ :=
    evaluate_mptInsert_advance middle live extensions branches registered node slot level nextNode nextSlot nextLevel
      ((kept _ (by decide)).trans nodeLocal) ((kept _ (by decide)).trans slotLocal)
      ((kept _ (by decide)).trans levelLocal) ((kept _ (by decide)).trans nextNodeLocal)
      ((kept _ (by decide)).trans nextSlotLocal) ((kept _ (by decide)).trans nextLevelLocal)
      childValid (Or.inr slotTyped)
  have postSlot : TrieChildSlot post extensions branches nextSlot :=
    slotTyped.after_length_frame (by intro node member; exact congrFun memory _)
  refine ⟨post,root,?_,registry,postClock.trans clock,
    (framed _ (by decide) (by decide) (by decide)).trans rootLocal,rootValid,
    atNode,childValid,atSlot,?_,atLevel,?_⟩
  · rw [source_mptInsert_finish]
    exact evaluate_seq_none commit advance
  · exact postSlot
  · intro name notResult notNode notSlot notLevel
    exact (framed name notNode notSlot notLevel).trans (kept name notResult)

#print axioms source_mptInsert_finish
#print axioms evaluate_mptInsert_finish
end InitECandidate.Runtime
