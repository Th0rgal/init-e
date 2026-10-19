import InitECandidate.Runtime.WitnessBranchSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_witness_branch_finish_entry : witnessBranchFinishAt 0 =
  .dec (ofString "arr2") .one (.load .one (.op .add [.var .local (ofString "top"),.const 24])) (witnessBranchFinishAt 1) := by
  simp only [witnessBranchFinishAt,witnessBranchFinish,witnessBranchAt,witnessUnwindBranch,witnessUnwindNonempty,
    decodeWitnessNodeUnwindMode,decodeWitnessNodeIteration,decodeWitnessNodeBodyAt,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_witness_branch_finish_parse : witnessBranchFinishAt 1 =
  .decCall (ofString "bv") (.comb [.one,.one,.one,.one]) (ofString "rlp_item")
    [.load .one (.op .add [.var .local (ofString "arr2"),.panop .mul [.const 16,.const 16]]),
     .load .one (.op .add [.var .local (ofString "arr2"),.panop .mul [.const 16,.const 16],.const 8])]
    (witnessBranchFinishAt 2) := by
  simp only [witnessBranchFinishAt,witnessBranchFinish,witnessBranchAt,witnessUnwindBranch,witnessUnwindNonempty,
    decodeWitnessNodeUnwindMode,decodeWitnessNodeIteration,decodeWitnessNodeBodyAt,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_witness_branch_finish_occupancy : witnessBranchFinishAt 2 =
  .dec (ofString "occ") .one (.load .one (.op .add [.var .local (ofString "top"),.const 40])) (witnessBranchFinishAt 3) := by
  simp only [witnessBranchFinishAt,witnessBranchFinish,witnessBranchAt,witnessUnwindBranch,witnessUnwindNonempty,
    decodeWitnessNodeUnwindMode,decodeWitnessNodeIteration,decodeWitnessNodeBodyAt,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_witness_branch_finish_value : witnessBranchFinishAt 3 =
  .seq (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "bv"))) (.const 0))
    (.seq (.store (.op .add [.var .local (ofString "br"),.const 160]) (.rfield 1 (.var .local (ofString "bv"))))
      (.seq (.store (.op .add [.var .local (ofString "br"),.const 168]) (.rfield 2 (.var .local (ofString "bv"))))
        (.ite (.cmp .notEqual (.rfield 2 (.var .local (ofString "bv"))) (.const 0))
          (.assign .local (ofString "occ") (.op .add [.var .local (ofString "occ"),.const 1])) .skip))) .skip)
    (witnessBranchFinishAt 4) := by
  simp only [witnessBranchFinishAt,witnessBranchFinish,witnessBranchAt,witnessUnwindBranch,witnessUnwindNonempty,
    decodeWitnessNodeUnwindMode,decodeWitnessNodeIteration,decodeWitnessNodeBodyAt,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_witness_branch_finish_guard : witnessBranchFinishAt 4 =
  .seq (.ite (.cmp .lower (.var .local (ofString "occ")) (.const 2))
    (.call (some (none,none)) (ofString "mpt_fail") [.const 9]) .skip) (witnessBranchFinishAt 5) := by
  simp only [witnessBranchFinishAt,witnessBranchFinish,witnessBranchAt,witnessUnwindBranch,witnessUnwindNonempty,
    decodeWitnessNodeUnwindMode,decodeWitnessNodeIteration,decodeWitnessNodeBodyAt,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_witness_branch_finish_stores : witnessBranchFinishAt 5 =
  .seq (.store (.op .add [.var .local (ofString "br"),.const 8])
    (.load .one (.op .add [.var .local (ofString "top"),.const 48])))
  (.seq (.store (.op .add [.var .local (ofString "br"),.const 16])
    (.load .one (.op .add [.var .local (ofString "top"),.const 56])))
  (.seq (.assign .local (ofString "top") (.load .one (.op .add [.var .local (ofString "top"),.const 0])))
    (.assign .local (ofString "result") (.var .local (ofString "br"))))) := by
  simp only [witnessBranchFinishAt,witnessBranchFinish,witnessBranchAt,witnessUnwindBranch,witnessUnwindNonempty,
    decodeWitnessNodeUnwindMode,decodeWitnessNodeIteration,decodeWitnessNodeBodyAt,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_witness_branch_finish_entry
#print axioms source_witness_branch_finish_parse
#print axioms source_witness_branch_finish_occupancy
#print axioms source_witness_branch_finish_value
#print axioms source_witness_branch_finish_guard
#print axioms source_witness_branch_finish_stores
end InitECandidate.Runtime
