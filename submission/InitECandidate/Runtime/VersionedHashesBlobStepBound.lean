import InitECandidate.Runtime.VersionedHashesBlobProgress
import InitECandidate.Runtime.MemeqDecCall64Bound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- One original 32-byte comparison, its guards, and both index assignments
have source-clock cost at most 129, including memeq errors and early returns. -/
theorem versioned_hashes_blob_step_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (left right : BitVec 64) (code : state.code = originalRuntimeCode)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) versionedHashesCompareArguments =
      some [.val (.word left),.val (.word right),.val (.word (32 : BitVec 64))])
    (budget : 129 ≤ state.clock) :
    let output := evaluateHOLFiniteState state versionedHashesBlobStep
    state.clock ≤ output.2.clock + 129 ∧ output.2.clock ≤ state.clock ∧ output.1 ≠ some .timeOut := by
  have compared := evaluate_memeq_decCall64_straight_bounded state (ofString "eq") versionedHashesCompareTail (by rfl)
    (.op .add [.load .one (.op .add [.var .local (ofString "tx"),.const 256]),.panop .mul [.var .local (ofString "j"),.const 32]])
    (.op .add [.var .local (ofString "vh"),.panop .mul [.var .local (ofString "k"),.const 32]]) (.const 32) left right 32 code args (by decide) budget
  rw [source_versioned_hashes_blob_step,evaluateHOLFiniteState_seq_line780]
  unfold versionedHashesBlobGuard
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · rw [evaluateHOLFiniteState_skip]
      exact compared
    · rw [evaluateHOLFiniteState_return]
      simp only [evalHOLExact]
      split_ifs <;> dsimp only <;> exact ⟨by change state.clock ≤ state.clock + 129; omega,Nat.le_refl _,by simp⟩
  · dsimp only
    exact ⟨by omega,Nat.le_refl _,by simp⟩

#print axioms versioned_hashes_blob_step_bounded
end InitECandidate.Runtime
