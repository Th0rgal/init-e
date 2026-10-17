import InitECandidate.Runtime.MptInsertBranchValue
import InitECandidate.Runtime.TrieExtensionChildStore
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def mptInsertCommit : ProgHOL 64 :=
  match mptInsertLoopStep with
  | .dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.seq _ (.seq _ (.seq commit _)))))) => commit
  | _ => .skip

theorem source_mptInsert_commit : mptInsertCommit =
    .ite (.cmp .equal (.var .local (ofString "slot")) (.const 0))
      (.assign .local (ofString "result") (.var .local (ofString "r")))
      (.store (.var .local (ofString "slot")) (.var .local (ofString "r"))) := by
  simp only [mptInsertCommit,mptInsertLoopStep,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Original insertion commits a live/null result either to its root local or
to a typed child backlink, preserving the complete traversal registry. -/
theorem evaluate_mptInsert_commit {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
    (layout : TrieNodeLayout live extensions branches size)
    (registry : TrieWalkRegistry live extensions branches state)
    (slot result oldRoot : BitVec 64)
    (slotLocal : state.locals.lookup (ofString "slot") = some (.val (.word slot)))
    (resultLocal : state.locals.lookup (ofString "r") = some (.val (.word result)))
    (rootLocal : state.locals.lookup (ofString "result") = some (.val (.word oldRoot)))
    (resultValid : result = 0 ∨ result ∈ live) (rootValid : oldRoot = 0 ∨ oldRoot ∈ live)
    (typedSlot : slot ≠ 0 → TrieChildSlot state extensions branches slot)
    (domain : slot ≠ 0 → state.memaddrs slot) :
    ∃ post root, evaluateHOLFiniteState state mptInsertCommit = (none,post) ∧
      TrieWalkRegistry live extensions branches post ∧ post.clock = state.clock ∧
      post.locals.lookup (ofString "result") = some (.val (.word root)) ∧ (root = 0 ∨ root ∈ live) := by
  rw [source_mptInsert_commit,evaluateHOLFiniteState_ite]
  by_cases zero : slot = 0
  · have guard : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .equal (.var .local (ofString "slot")) (.const 0)) = some (.val (.word (1 : BitVec 64))) := by
      simp [evalHOLExact,slotLocal,zero,Compiler.Encoders.Asm.wordCmpHOL]
    rw [guard]
    have assignment := evaluate_local_word_assignment state (ofString "result") (.var .local (ofString "r")) oldRoot result rootLocal resultLocal
    refine ⟨setVarHOLFinite (ofString "result") (.val (.word result)) state,result,?_,registry.after_memory rfl,rfl,?_,resultValid⟩
    · simpa using assignment
    · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · have guard : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .equal (.var .local (ofString "slot")) (.const 0)) = some (.val (.word (0 : BitVec 64))) := by
      simp [evalHOLExact,slotLocal,Compiler.Encoders.Asm.wordCmpHOL]
      exact zero
    rw [guard]
    have store := evaluate_store_word state slot result (.var .local (ofString "slot")) (.var .local (ofString "r")) slotLocal resultLocal (domain zero)
    exact ⟨sourceWriteWord state slot result,oldRoot,store,
      registry.write_slot state live extensions branches size layout slot result (typedSlot zero) resultValid,rfl,rootLocal,rootValid⟩

#print axioms source_mptInsert_commit
#print axioms evaluate_mptInsert_commit
end InitECandidate.Runtime
