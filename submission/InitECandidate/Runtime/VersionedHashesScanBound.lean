import InitECandidate.Runtime.VersionedHashesBlobInitializationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A deliberately loose uniform bound, valid even for arbitrary header words. -/
def versionedHashesScanCost : Nat := 2^64 * 130

theorem evaluate_versioned_hashes_blob_header_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (tx vh cursor : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (vhLocal : state.locals.lookup (ofString "vh") = some (.val (.word vh)))
    (cursorLocal : state.locals.lookup (ofString "k") = some (.val (.word cursor)))
    (code : state.code = originalRuntimeCode) (budget : versionedHashesScanCost ≤ state.clock) :
    let output := evaluateHOLFiniteState state (.dec (ofString "nb") .one
      (.load .one (.op .add [.var .local (ofString "tx"),.const 264]))
      (.dec (ofString "j") .one (.const 0) versionedHashesBlobLoop))
    state.clock ≤ output.2.clock + versionedHashesScanCost ∧ output.2.clock ≤ state.clock ∧ output.1 ≠ some .timeOut := by
  classical
  by_cases domain : state.memaddrs (tx + 264#64)
  · cases cell : state.memory (tx + 264#64) with
    | word count =>
      have loaded : @evalHOLExact 64 F _ state.toExact
          (fun address => Classical.propDecidable (state.memaddrs address))
          (.load .one (.op .add [.var .local (ofString "tx"),.const 264])) = some (.val (.word count)) := by
        simp [evalHOLExact,evalListHOLExact,txLocal,wordOpHOL,wordOp,valueIsWord,valueWord,
          isWfShapeExactHOL,memLoadHOLExact,domain,cell]
      have cost : count.toNat * 130 ≤ versionedHashesScanCost := by
        exact Nat.mul_le_mul_right 130 (Nat.le_of_lt count.isLt)
      have bounded := evaluate_versioned_hashes_blob_count_loaded_bounded state count tx vh cursor loaded txLocal vhLocal cursorLocal code (by omega)
      dsimp only at bounded ⊢
      exact ⟨by omega,bounded.2⟩
  · rw [evaluateHOLFiniteState_dec_total]
    have loaded : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.load .one (.op .add [.var .local (ofString "tx"),.const 264])) = none := by
      simp [evalHOLExact,evalListHOLExact,txLocal,wordOpHOL,wordOp,valueIsWord,valueWord,
        isWfShapeExactHOL,memLoadHOLExact,domain]
    dsimp only
    rw [loaded]
    exact ⟨by change state.clock ≤ state.clock + versionedHashesScanCost; omega,Nat.le_refl _,by simp⟩

/-- The original conditional scan includes failed guards, failed header loads,
comparison errors and early returns within one uniform finite source bound. -/
theorem evaluate_versioned_hashes_scan_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (tx vh cursor : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (vhLocal : state.locals.lookup (ofString "vh") = some (.val (.word vh)))
    (cursorLocal : state.locals.lookup (ofString "k") = some (.val (.word cursor)))
    (code : state.code = originalRuntimeCode) (budget : versionedHashesScanCost ≤ state.clock) :
    let output := evaluateHOLFiniteState state versionedHashesScan
    state.clock ≤ output.2.clock + versionedHashesScanCost ∧ output.2.clock ≤ state.clock ∧ output.1 ≠ some .timeOut := by
  have bounded := evaluate_versioned_hashes_blob_header_bounded state tx vh cursor txLocal vhLocal cursorLocal code budget
  rw [source_versioned_hashes_scan,evaluateHOLFiniteState_ite]
  split
  · split
    · rw [evaluateHOLFiniteState_skip]
      exact ⟨by change state.clock ≤ state.clock + versionedHashesScanCost; omega,Nat.le_refl _,by simp⟩
    · exact bounded
  · exact ⟨by change state.clock ≤ state.clock + versionedHashesScanCost; omega,Nat.le_refl _,by simp⟩

#print axioms evaluate_versioned_hashes_blob_header_bounded
#print axioms evaluate_versioned_hashes_scan_bounded
end InitECandidate.Runtime
