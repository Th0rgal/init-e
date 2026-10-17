import InitECandidate.Runtime.TrieWalkLeafTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def trieWalkBranchBranch : ProgHOL 64 :=
  match trieWalkStep with
  | .dec _ _ _ (.seq _ (.seq _ (.ite _ _ no))) => no
  | _ => .skip

def trieWalkBranchValueReturn : ProgHOL 64 :=
  match trieWalkBranchBranch with | .seq (.ite _ yes _) _ => yes | _ => .skip

def trieWalkBranchAdvance : ProgHOL 64 :=
  match trieWalkBranchBranch with | .seq _ tail => tail | _ => .skip

def trieWalkBranchNodeExpression : ExpHOL 64 :=
  match trieWalkBranchAdvance with | .seq (.assign _ _ value) _ => value | _ => .const 0

theorem source_trieWalk_branch_branch : trieWalkBranchBranch =
    .seq (.ite (.cmp .equal (.var .local (ofString "pos")) (.var .local (ofString "nlen")))
      trieWalkBranchValueReturn .skip) trieWalkBranchAdvance := by
  simp only [trieWalkBranchBranch,trieWalkBranchValueReturn,trieWalkBranchAdvance,trieWalkStep,trieWalkLoop,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_trieWalk_branch_advance : trieWalkBranchAdvance =
    .seq (.assign .local (ofString "node") trieWalkBranchNodeExpression)
      (.assign .local (ofString "pos") (.op .add [.var .local (ofString "pos"),.const 1])) := by
  simp only [trieWalkBranchAdvance,trieWalkBranchBranch,trieWalkBranchNodeExpression,trieWalkStep,trieWalkLoop,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem trieWalk_branch_branch_straightLine : straightLine trieWalkBranchBranch = true := by
  simp only [trieWalkBranchBranch,trieWalkStep,trieWalkLoop,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Reading a branch value is terminal, including every possible load error. -/
theorem evaluate_trieWalk_branch_value_terminal {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state trieWalkBranchValueReturn).1 ≠ none := by
  simp only [trieWalkBranchValueReturn,trieWalkBranchBranch,trieWalkStep,trieWalkLoop,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  apply evaluate_declaration_terminal
  intro next
  apply evaluate_sequence_terminal
  intro finalState
  exact evaluate_return_terminal finalState _

/-- Branch nodes have no nested call/loop cost, even on invalid memory. -/
theorem evaluate_trieWalk_branch_branch_clock {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state trieWalkBranchBranch).2.clock = state.clock ∧
    (evaluateHOLFiniteState state trieWalkBranchBranch).1 ≠ some .timeOut :=
  ⟨clockPreserving_of_straightLine _ trieWalk_branch_branch_straightLine state,
   evaluate_straightLine_no_timeout _ trieWalk_branch_branch_straightLine state⟩

#print axioms source_trieWalk_branch_branch
#print axioms source_trieWalk_branch_advance
#print axioms trieWalk_branch_branch_straightLine
#print axioms evaluate_trieWalk_branch_value_terminal
#print axioms evaluate_trieWalk_branch_branch_clock
end InitECandidate.Runtime
