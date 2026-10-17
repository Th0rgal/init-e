import InitECandidate.Runtime.MptInsertCommitPrepared
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original insertion commits a live/null result either to its root local or
to a typed child backlink, preserving the complete traversal registry and a prepared next backlink. -/
theorem evaluate_mptInsert_commit_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
    (layout : TrieNodeLayout live extensions branches size)
    (registry : TrieWalkRegistry live extensions branches state)
    (watched : BitVec 64) (prepared : TrieChildSlot state extensions branches watched)
    (slot result oldRoot : BitVec 64)
    (slotLocal : state.locals.lookup (ofString "slot") = some (.val (.word slot)))
    (resultLocal : state.locals.lookup (ofString "r") = some (.val (.word result)))
    (rootLocal : state.locals.lookup (ofString "result") = some (.val (.word oldRoot)))
    (resultValid : result = 0 ∨ result ∈ live) (rootValid : oldRoot = 0 ∨ oldRoot ∈ live)
    (typedSlot : slot ≠ 0 → TrieChildSlot state extensions branches slot)
    (domain : slot ≠ 0 → state.memaddrs slot) :
    ∃ post root, evaluateHOLFiniteState state mptInsertCommit = (none,post) ∧
      TrieWalkRegistry live extensions branches post ∧ post.clock = state.clock ∧
      post.locals.lookup (ofString "result") = some (.val (.word root)) ∧ (root = 0 ∨ root ∈ live) ∧ TrieChildSlot post extensions branches watched ∧
      (∀ name, name ≠ ofString "result" → post.locals.lookup name = state.locals.lookup name) := by
  rw [source_mptInsert_commit,evaluateHOLFiniteState_ite]
  by_cases zero : slot = 0
  · have guard : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .equal (.var .local (ofString "slot")) (.const 0)) = some (.val (.word (1 : BitVec 64))) := by
      simp [evalHOLExact,slotLocal,zero,Compiler.Encoders.Asm.wordCmpHOL]
    rw [guard]
    have assignment := evaluate_local_word_assignment state (ofString "result") (.var .local (ofString "r")) oldRoot result rootLocal resultLocal
    refine ⟨setVarHOLFinite (ofString "result") (.val (.word result)) state,result,?_,registry.after_memory rfl,rfl,?_,resultValid,prepared.after_length_frame (by intro node member; rfl),?_⟩
    · simpa using assignment
    · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · intro name different
      simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  · have guard : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .equal (.var .local (ofString "slot")) (.const 0)) = some (.val (.word (0 : BitVec 64))) := by
      simp [evalHOLExact,slotLocal,Compiler.Encoders.Asm.wordCmpHOL]
      exact zero
    rw [guard]
    have store := evaluate_store_word state slot result (.var .local (ofString "slot")) (.var .local (ofString "r")) slotLocal resultLocal (domain zero)
    exact ⟨sourceWriteWord state slot result,oldRoot,store,
      registry.write_slot state live extensions branches size layout slot result (typedSlot zero) resultValid,rfl,rootLocal,rootValid,TrieChildSlot.after_slot_store state live extensions branches size layout slot watched result (typedSlot zero) prepared,(by intro name different; rfl)⟩

#print axioms evaluate_mptInsert_commit_frame
end InitECandidate.Runtime
