import InitECandidate.Runtime.KeccakMainLoopBound
import InitECandidate.Runtime.KeccakGlobalsFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The full-block loop retains the global workspaces in every outcome. -/
theorem keccak_main_loop_globals : OriginalGlobalsFrame keccakMainLoop := by
  rw [source_keccak_main_loop]
  apply originalGlobalsFrame_while
  rw [source_keccak_main_body]
  apply originalGlobalsFrame_sequence
  · exact keccakAbsorb_call_globals_frame _
  · exact originalGlobalsFrame_leaf _ (by intro watched; rfl)

theorem runBounded_keccak_main_loop {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer source size : BitVec 64) (code : state.code = originalRuntimeCode)
    (atI : state.locals.lookup (ofString "i") = some (.val (.word 0)))
    (atN : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (atP : state.locals.lookup (ofString "p") = some (.val (.word source)))
    (atStp : state.locals.lookup (ofString "stp") = some (.val (.word pointer)))
    (small : size.toNat ≤ 134217712) (budget : size.toNat * 20 ≤ state.clock) :
    RunBounded state keccakMainLoop (size.toNat * 20) := by
  have valid : KeccakMainRank pointer source size state size.toNat :=
    ⟨0,atI,atN,atP,atStp,(by simp),(by decide),(by simp)⟩
  have outcome := keccak_main_loop_ranked pointer source size small _ state code valid budget
  exact ⟨outcome.1,outcome.2.1,outcome.2.2.1⟩

/-- A normal full-block exit leaves an aligned index and fewer than 136 bytes
for padding, preserving every other caller local and all globals. -/
theorem keccak_main_loop_normal_result {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer source size : BitVec 64) (code : state.code = originalRuntimeCode)
    (atI : state.locals.lookup (ofString "i") = some (.val (.word 0)))
    (atN : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (atP : state.locals.lookup (ofString "p") = some (.val (.word source)))
    (atStp : state.locals.lookup (ofString "stp") = some (.val (.word pointer)))
    (small : size.toNat ≤ 134217712) (budget : size.toNat * 20 ≤ state.clock)
    (run : evaluateHOLFiniteState state keccakMainLoop = (none,post)) :
    (∃ index : BitVec 64, post.locals.lookup (ofString "i") = some (.val (.word index)) ∧
      index.toNat ≤ size.toNat ∧ index.toNat % 8 = 0 ∧ size.toNat - index.toNat < 136) ∧
    post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧
    (∀ key : MlS, key ≠ ofString "i" → post.locals.lookup key = state.locals.lookup key) := by
  have valid : KeccakMainRank pointer source size state size.toNat :=
    ⟨0,atI,atN,atP,atStp,(by simp),(by decide),(by simp)⟩
  have outcome := keccak_main_loop_ranked pointer source size small _ state code valid budget
  rw [run] at outcome
  obtain ⟨rank,⟨index,idx,n,p,stp,inside,aligned,ranking⟩,installed,exit⟩ := outcome.2.2.2 rfl
  have zero : evalHOLFinite post (h := fun a => Classical.propDecidable (post.memaddrs a)) keccakFullCondition =
      some (.val (.word 0)) := by rcases exit with zero | impossible; exact zero; exact impossible.elim
  rw [eval_keccak_full_condition post index size idx n inside small] at zero
  have tailSmall : size.toNat - index.toNat < 136 := by
    by_cases active : index.toNat + 136 ≤ size.toNat
    · simp [active] at zero
    · omega
  have globals := keccak_main_loop_globals state code
  have metadata := evaluateHOLFiniteState_metadata state keccakMainLoop
  rw [run] at globals metadata
  refine ⟨⟨index,idx,inside,aligned,tailSmall⟩,globals,installed,metadata.2.1,?_⟩
  intro key different
  have avoids : avoidsLocal key keccakMainLoop = true := by
    rw [source_keccak_main_loop]
    simp [avoidsLocal,source_keccak_main_body,Ne.symm different]
  have kept := evaluate_avoidsLocal_flowing key keccakMainLoop avoids state (by rw [run]; exact Or.inl rfl)
  rw [run] at kept
  exact kept

#print axioms keccak_main_loop_globals
#print axioms runBounded_keccak_main_loop
#print axioms keccak_main_loop_normal_result
end InitECandidate.Runtime
