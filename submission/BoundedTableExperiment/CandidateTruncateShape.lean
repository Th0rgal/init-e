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
set_option maxHeartbeats 1000000

/-! ## expression helpers -/

def loc (n : String) : ExpHOL 64 := .var .local (ofString n)
def off (n : String) (d : BitVec 64) : ExpHOL 64 := .op .add [loc n,.const d]
def lw (e : ExpHOL 64) : ExpHOL 64 := .load .one e
def idx8 (base index : ExpHOL 64) : ExpHOL 64 := .op .add [base,.panop .mul [index,.const 8]]

/-- `htab_key_ptr t leaf`, used as the body of the loop step. -/
def truncateKeyCall : ProgHOL 64 :=
  .decCall (ofString "key") .one (ofString "htab_key_ptr") [loc "t",loc "leaf"]
    (.call (some (none, none)) (ofString "htab_del") [loc "t",loc "key"])

/-- One iteration: pop the last key and delete it. -/
def truncateStep : ProgHOL 64 :=
  .dec (ofString "pos") .one (.op .sub [lw (off "t" 24),.const 1])
    (.dec (ofString "leaf") .one (lw (idx8 (lw (off "t" 56)) (loc "pos")))
      truncateKeyCall)

/-- Loop until `n` keys are left. -/
def truncateWhile : ProgHOL 64 :=
  .while (.cmp .lower (loc "n") (lw (off "t" 24))) truncateStep

def truncateReturn : ProgHOL 64 := .return (.const 0)

def truncateBody : ProgHOL 64 := .seq truncateWhile truncateReturn

/-! ## pinning theorem -/

theorem candidateTruncate_body :
    sourceFunctionBody Candidate.guestFn_htab_truncate = truncateBody := by
  simp only [sourceFunctionBody, declToHOL_eq, declToHOLStructural, funDeclToHOLStructural,
    Candidate.guestFn_htab_truncate, truncateBody, truncateWhile, truncateStep,
    truncateKeyCall, truncateReturn,
    loc, off, lw, idx8,
    progToHOLStructural, expToHOLStructural, expListToHOLStructural, shapeToHOLStructural,
    paramToHOLStructural, List.map_cons, List.map_nil, Option.map]
  rfl

/-! ## the literal shape -/

theorem candidateTruncate_body_scopes :
    sourceFunctionBody Candidate.guestFn_htab_truncate =
      .seq (.while (.cmp .lower (loc "n") (lw (off "t" 24))) truncateStep)
        (.return (.const 0)) :=
  candidateTruncate_body

theorem candidateTruncate_while :
    truncateWhile = .while (.cmp .lower (loc "n") (lw (off "t" 24))) truncateStep := rfl

theorem candidateTruncate_step :
    truncateStep =
      .dec (ofString "pos") .one (.op .sub [lw (off "t" 24),.const 1])
        (.dec (ofString "leaf") .one (lw (idx8 (lw (off "t" 56)) (loc "pos")))
          (.decCall (ofString "key") .one (ofString "htab_key_ptr") [loc "t",loc "leaf"]
            (.call (some (none, none)) (ofString "htab_del") [loc "t",loc "key"]))) := rfl

theorem candidateTruncate_keyCall :
    truncateKeyCall =
      .decCall (ofString "key") .one (ofString "htab_key_ptr") [loc "t",loc "leaf"]
        (.call (some (none, none)) (ofString "htab_del") [loc "t",loc "key"]) := rfl

theorem candidateTruncate_return : truncateReturn = .return (.const 0) := rfl

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidateTruncate_body
