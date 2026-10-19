import InitECandidate.Runtime.WitnessExtensionSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def witnessBranchAt (n : Nat) : ProgHOL 64 := stateInitSpineDrop n witnessUnwindBranch

def witnessBranchMore : ProgHOL 64 :=
  match witnessBranchAt 5 with | .ite _ more _ => more | _ => .skip

def witnessBranchFinish : ProgHOL 64 :=
  match witnessBranchAt 5 with | .ite _ _ finish => finish | _ => .skip

def witnessBranchFinishAt (n : Nat) : ProgHOL 64 := stateInitSpineDrop n witnessBranchFinish

theorem source_witness_branch_entry : witnessBranchAt 0 =
  .dec (ofString "br") .one (.load .one (.op .add [.var .local (ofString "top"),.const 16]))
    (.dec (ofString "i") .one (.load .one (.op .add [.var .local (ofString "top"),.const 32]))
      (witnessBranchAt 2)) := by
  simp only [witnessBranchAt,witnessUnwindBranch,witnessUnwindNonempty,decodeWitnessNodeUnwindMode,
    decodeWitnessNodeIteration,decodeWitnessNodeBodyAt,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_witness_branch_child_store : witnessBranchAt 2 =
  .seq (.store (.op .add [.var .local (ofString "br"),.const 32,
    .panop .mul [.var .local (ofString "i"),.const 8]]) (.var .local (ofString "result"))) (witnessBranchAt 3) := by
  simp only [witnessBranchAt,witnessUnwindBranch,witnessUnwindNonempty,decodeWitnessNodeUnwindMode,
    decodeWitnessNodeIteration,decodeWitnessNodeBodyAt,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_witness_branch_occupancy : witnessBranchAt 3 =
  .seq (.ite (.cmp .notEqual (.var .local (ofString "result")) (.const 0))
    (.store (.op .add [.var .local (ofString "top"),.const 40])
      (.op .add [.load .one (.op .add [.var .local (ofString "top"),.const 40]),.const 1])) .skip)
    (witnessBranchAt 4) := by
  simp only [witnessBranchAt,witnessUnwindBranch,witnessUnwindNonempty,decodeWitnessNodeUnwindMode,
    decodeWitnessNodeIteration,decodeWitnessNodeBodyAt,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_witness_branch_increment : witnessBranchAt 4 =
  .seq (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])) (witnessBranchAt 5) := by
  simp only [witnessBranchAt,witnessUnwindBranch,witnessUnwindNonempty,decodeWitnessNodeUnwindMode,
    decodeWitnessNodeIteration,decodeWitnessNodeBodyAt,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_witness_branch_dispatch : witnessBranchAt 5 =
  .ite (.cmp .less (.var .local (ofString "i")) (.const 16)) witnessBranchMore witnessBranchFinish := by
  simp only [witnessBranchMore,witnessBranchFinish]
  simp only [witnessBranchAt,witnessUnwindBranch,witnessUnwindNonempty,decodeWitnessNodeUnwindMode,
    decodeWitnessNodeIteration,decodeWitnessNodeBodyAt,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_witness_branch_more : witnessBranchMore =
  .seq (.store (.op .add [.var .local (ofString "top"),.const 32]) (.var .local (ofString "i")))
    (.seq (.assign .local (ofString "slot") (.var .local (ofString "i")))
      (.assign .local (ofString "mode") (.const 2))) := by
  simp only [witnessBranchMore,witnessBranchAt,witnessUnwindBranch,witnessUnwindNonempty,decodeWitnessNodeUnwindMode,
    decodeWitnessNodeIteration,decodeWitnessNodeBodyAt,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_witness_branch_entry
#print axioms source_witness_branch_child_store
#print axioms source_witness_branch_occupancy
#print axioms source_witness_branch_increment
#print axioms source_witness_branch_dispatch
#print axioms source_witness_branch_more
end InitECandidate.Runtime
