import InitECandidate.Runtime.WitnessBranchFinishSource
import InitECandidate.Runtime.DecodeStepLeafValueUniformBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem witness_branch_finish_stores_bounded : ProgBounded (witnessBranchFinishAt 5) 0 := by
  apply ProgBounded.straight
  rw [source_witness_branch_finish_stores]
  rfl

theorem witness_branch_finish_guard_bounded : ProgBounded (witnessBranchFinishAt 4) 1 := by
  rw [source_witness_branch_finish_guard]
  exact ProgBounded.seq (mpt_fail_guard_uniform_bounded _ 9) witness_branch_finish_stores_bounded

theorem witness_branch_finish_value_bounded : ProgBounded (witnessBranchFinishAt 3) 1 := by
  rw [source_witness_branch_finish_value]
  have stores : ProgBounded
      (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "bv"))) (.const 0))
        (.seq (.store (.op .add [.var .local (ofString "br"),.const 160]) (.rfield 1 (.var .local (ofString "bv"))))
          (.seq (.store (.op .add [.var .local (ofString "br"),.const 168]) (.rfield 2 (.var .local (ofString "bv"))))
            (.ite (.cmp .notEqual (.rfield 2 (.var .local (ofString "bv"))) (.const 0))
              (.assign .local (ofString "occ") (.op .add [.var .local (ofString "occ"),.const 1])) .skip))) .skip) 0 :=
    ProgBounded.straight _ rfl
  intro F state code budget
  simpa only [Nat.zero_add] using (ProgBounded.seq stores witness_branch_finish_guard_bounded) state code (by simpa using budget)

theorem witness_branch_finish_tail_bounded : ProgBounded (witnessBranchFinishAt 2) 1 := by
  rw [source_witness_branch_finish_occupancy]
  exact ProgBounded.dec _ _ _ witness_branch_finish_value_bounded

#print axioms witness_branch_finish_stores_bounded
#print axioms witness_branch_finish_guard_bounded
#print axioms witness_branch_finish_value_bounded
#print axioms witness_branch_finish_tail_bounded
end InitECandidate.Runtime
