import InitECandidate.Runtime.PanStatementWork
import InitECandidate.Proofs.FrontendCodecComputation
import CandidateAst

namespace BoundedTableExperiment
open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open InitECandidate.Proofs.FrontendCodecComputation
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000

/-- (b) The codec body of a function declaration is the structurally
recursive translation of its `Prog`, which the kernel reduces. -/
theorem sourceFunctionBody_function (d : FunDeclOf 64) :
    sourceFunctionBody (.function d) = progToHOLStructural d.body := by
  unfold sourceFunctionBody
  rw [declToHOL_eq]
  rfl

/-- The exact HOL body of the candidate `htab_set`. -/
def candidateHtabSetBody : ProgHOL 64 :=
  match Candidate.guestFn_htab_set with
  | .function d => progToHOLStructural d.body
  | _ => .skip

/-- The body under the leading `cap` scope. -/
def candidateHtabSetRest : ProgHOL 64 :=
  match candidateHtabSetBody with
  | .dec _ _ _ rest => rest
  | _ => .skip

/-- (a) Top-level shape of the candidate `htab_set`: one `dec` scope, `cap`. -/
theorem candidateHtabSet_body :
    sourceFunctionBody Candidate.guestFn_htab_set =
      .dec (ofString "cap") .one
        (.load .one (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 16)]))
        candidateHtabSetRest := by
  unfold sourceFunctionBody
  rw [declToHOL_eq]
  rfl

/-- First/only split of a `seq`, defaulting to `skip`. -/
def headOf (p : ProgHOL 64) : ProgHOL 64 :=
  match p with
  | .seq first _ => first
  | _ => .skip

def tailOf (p : ProgHOL 64) : ProgHOL 64 :=
  match p with
  | .seq _ second => second
  | _ => .skip

/-- The two statements of the `cap` scope body. -/
def candidateHtabSetMiss : ProgHOL 64 := headOf candidateHtabSetRest

def candidateHtabSetFound : ProgHOL 64 := tailOf candidateHtabSetRest

/-- One level deeper: the `cap` scope body is a two-arm `seq`. -/
theorem candidateHtabSet_body_seq :
    sourceFunctionBody Candidate.guestFn_htab_set =
      .dec (ofString "cap") .one
        (.load .one (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 16)]))
        (.seq candidateHtabSetMiss candidateHtabSetFound) := by
  unfold sourceFunctionBody
  rw [declToHOL_eq]
  rfl

/-- `cases` on a `StatementRun` of the candidate body exposes the `dec` rules. -/
example {F : Type} (fn : MlS) (s : PanSemStateFiniteExact 64 F)
    (r : Option (PanSemResultExact 64)) (post : PanSemStateFiniteExact 64 F)
    (ev : List WorkEvent)
    (run : StatementRun fn s (sourceFunctionBody Candidate.guestFn_htab_set) r post ev) :
    True := by
  rw [candidateHtabSet_body] at run
  cases run with
  | declareValue init shapeMatch bodyRun => trivial
  | declareMismatch init mismatch => trivial
  | declareFailure init => trivial

/-- Same, one level deeper: `declareValue` then `seqNext`/`seqStop`. -/
example {F : Type} (fn : MlS) (s : PanSemStateFiniteExact 64 F)
    (r : Option (PanSemResultExact 64)) (post : PanSemStateFiniteExact 64 F)
    (ev : List WorkEvent)
    (run : StatementRun fn s (sourceFunctionBody Candidate.guestFn_htab_set) r post ev) :
    True := by
  rw [candidateHtabSet_body_seq] at run
  cases run with
  | declareValue init shapeMatch bodyRun =>
    cases bodyRun with
    | seqNext one two => trivial
    | seqStop terminal one => trivial
  | declareMismatch init mismatch => trivial
  | declareFailure init => trivial

/-- The root-empty check branch of `htab_set`. -/
def candidateHtabSetRootCheck : ExpHOL 64 :=
  match candidateHtabSetMiss with
  | .ite condition _ _ => condition
  | _ => .const (BitVec.ofNat 64 0)

def candidateHtabSetRootThen : ProgHOL 64 :=
  match candidateHtabSetMiss with
  | .ite _ yes _ => yes
  | _ => .skip

def candidateHtabSetRootElse : ProgHOL 64 :=
  match candidateHtabSetMiss with
  | .ite _ _ no => no
  | _ => .skip

/-- The miss branch is the root-empty `ite`. -/
theorem candidateHtabSet_miss_eq :
    candidateHtabSetMiss =
      .ite candidateHtabSetRootCheck candidateHtabSetRootThen candidateHtabSetRootElse := by
  unfold candidateHtabSetMiss candidateHtabSetRest candidateHtabSetBody headOf
  rfl

/-- The found branch is the `htab_find_leaf_path` call. -/
def candidateHtabSetLeafBody : ProgHOL 64 :=
  match candidateHtabSetFound with
  | .decCall _ _ _ _ body => body
  | _ => .skip

theorem candidateHtabSet_found_eq :
    candidateHtabSetFound =
      .decCall (ofString "leaf") .one (ofString "htab_find_leaf_path")
        [.var .local (ofString "t"), .var .local (ofString "key")]
        candidateHtabSetLeafBody := by
  unfold candidateHtabSetFound candidateHtabSetRest candidateHtabSetBody tailOf
  rfl

/-- Score of a `declareValue` event trace. -/
theorem declareValue_score (coeff : Work) (initEvents bodyEvents : List WorkEvent) :
    coeff.score (executionWork (.statement :: (initEvents ++ [.frame 1] ++ bodyEvents))) =
      coeff.statements + coeff.score (executionWork initEvents) + coeff.frameSlots +
      coeff.score (executionWork bodyEvents) := by
  rw [executionWork_score_cons, executionWork_score_append,
    executionWork_score_append]
  simp [executionWork, WorkEvent.units, Work.plus, Work.score]
  omega

/-- Score of an `ite` event trace. -/
theorem ite_score (coeff : Work) (branch : Nat) (guardEvents bodyEvents : List WorkEvent) :
    coeff.score (executionWork
      (.statement :: .cost (statementUnit + branch) :: (guardEvents ++ bodyEvents))) =
      coeff.statements + coeff.nativeCost * (statementUnit + branch) +
      coeff.score (executionWork guardEvents) +
      coeff.score (executionWork bodyEvents) := by
  rw [executionWork_score_cons, executionWork_score_cons,
    executionWork_score_append]
  simp [executionWork, WorkEvent.units, Work.plus, Work.score]
  omega

/-- Full top-level shape of the actual candidate `htab_set`: cap scope,
root-empty branch, then the `htab_find_leaf_path` call. -/
theorem candidateHtabSet_body_branches :
    sourceFunctionBody Candidate.guestFn_htab_set =
      .dec (ofString "cap") .one
        (.load .one (.op .add [.var .local (ofString "t"), .const (BitVec.ofNat 64 16)]))
        (.seq (.ite candidateHtabSetRootCheck candidateHtabSetRootThen candidateHtabSetRootElse)
          (.decCall (ofString "leaf") .one (ofString "htab_find_leaf_path")
            [.var .local (ofString "t"), .var .local (ofString "key")]
            candidateHtabSetLeafBody)) := by
  rw [candidateHtabSet_body_seq, candidateHtabSet_miss_eq, candidateHtabSet_found_eq]

end BoundedTableExperiment
#print axioms BoundedTableExperiment.candidateHtabSet_body_branches
#print axioms BoundedTableExperiment.declareValue_score
#print axioms BoundedTableExperiment.ite_score
