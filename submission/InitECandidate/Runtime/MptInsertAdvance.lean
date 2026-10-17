import InitECandidate.Runtime.MptInsertCommitPrepared
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def mptInsertAdvance : ProgHOL 64 :=
  match mptInsertLoopStep with
  | .dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.seq _ (.seq _ (.seq _ body)))))) => body
  | _ => .skip

theorem source_mptInsert_advance : mptInsertAdvance =
    .seq (.assign .local (ofString "node") (.var .local (ofString "next_node")))
      (.seq (.assign .local (ofString "slot") (.var .local (ofString "next_slot")))
        (.assign .local (ofString "level") (.var .local (ofString "next_level")))) := by
  simp only [mptInsertAdvance,mptInsertLoopStep,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The actual final assignments install the prepared node/backlink/level,
retaining registry facts and all other locals for the following iteration. -/
theorem evaluate_mptInsert_advance {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (registry : TrieWalkRegistry live extensions branches state)
    (node slot level nextNode nextSlot nextLevel : BitVec 64)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (slotLocal : state.locals.lookup (ofString "slot") = some (.val (.word slot)))
    (levelLocal : state.locals.lookup (ofString "level") = some (.val (.word level)))
    (nextNodeLocal : state.locals.lookup (ofString "next_node") = some (.val (.word nextNode)))
    (nextSlotLocal : state.locals.lookup (ofString "next_slot") = some (.val (.word nextSlot)))
    (nextLevelLocal : state.locals.lookup (ofString "next_level") = some (.val (.word nextLevel)))
    (childValid : nextNode = 0 ∨ nextNode ∈ live)
    (slotValid : nextSlot = 0 ∨ TrieChildSlot state extensions branches nextSlot) :
    ∃ post, evaluateHOLFiniteState state mptInsertAdvance = (none,post) ∧
      post.locals.lookup (ofString "node") = some (.val (.word nextNode)) ∧
      post.locals.lookup (ofString "slot") = some (.val (.word nextSlot)) ∧
      post.locals.lookup (ofString "level") = some (.val (.word nextLevel)) ∧
      (nextNode = 0 ∨ nextNode ∈ live) ∧ (nextSlot = 0 ∨ TrieChildSlot post extensions branches nextSlot) ∧
      TrieWalkRegistry live extensions branches post ∧ post.memory = state.memory ∧ post.clock = state.clock ∧
      (∀ name, name ≠ ofString "node" → name ≠ ofString "slot" → name ≠ ofString "level" →
        post.locals.lookup name = state.locals.lookup name) := by
  let s1 := setVarHOLFinite (ofString "node") (.val (.word nextNode)) state
  let s2 := setVarHOLFinite (ofString "slot") (.val (.word nextSlot)) s1
  let post := setVarHOLFinite (ofString "level") (.val (.word nextLevel)) s2
  have first := evaluate_local_word_assignment state (ofString "node") (.var .local (ofString "next_node"))
    node nextNode nodeLocal nextNodeLocal
  have oldSlot : s1.locals.lookup (ofString "slot") = some (.val (.word slot)) := by
    simpa [s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString] using slotLocal
  have newSlot : s1.locals.lookup (ofString "next_slot") = some (.val (.word nextSlot)) := by
    simpa [s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString] using nextSlotLocal
  have second := evaluate_local_word_assignment s1 (ofString "slot") (.var .local (ofString "next_slot"))
    slot nextSlot oldSlot newSlot
  have oldLevel : s2.locals.lookup (ofString "level") = some (.val (.word level)) := by
    simpa [s2,s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString] using levelLocal
  have newLevel : s2.locals.lookup (ofString "next_level") = some (.val (.word nextLevel)) := by
    simpa [s2,s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString] using nextLevelLocal
  have third := evaluate_local_word_assignment s2 (ofString "level") (.var .local (ofString "next_level"))
    level nextLevel oldLevel newLevel
  refine ⟨post,?_,?_,?_,?_,childValid,?_,registry.after_memory rfl,rfl,rfl,?_⟩
  · rw [source_mptInsert_advance]
    exact evaluate_seq_none first (evaluate_seq_none second third)
  · simp [post,s2,s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString]
  · simp [post,s2,s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ofString]
  · simp [post,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · rcases slotValid with zero | typed
    · exact Or.inl zero
    · exact Or.inr (typed.after_length_frame (by intro node member; rfl))
  · intro name notNode notSlot notLevel
    simp [post,s2,s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      Ne.symm notNode,Ne.symm notSlot,Ne.symm notLevel]

#print axioms source_mptInsert_advance
#print axioms evaluate_mptInsert_advance
end InitECandidate.Runtime
