import CandidateGuestAst
import InitECandidate.Runtime.SourceClock

namespace BoundedTableExperiment

open InitECandidate.Runtime
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 4000

/-- Head conversion equations for the production-to-HOL program conversion. -/
theorem progToHOL_decCall_eq (name : String) (shape : Shape) (f : String)
    (args : List (Exp (BitVec 64))) (rest : Prog (BitVec 64)) :
    progToHOL (.decCall name shape f args rest) =
      .decCall (ofString name) (shapeToHOL shape) (ofString f)
        (args.map expToHOL) (progToHOL rest) := by
  rw [progToHOL.eq_def]

theorem progToHOL_dec_eq (name : String) (shape : Shape)
    (value : Exp (BitVec 64)) (rest : Prog (BitVec 64)) :
    progToHOL (.dec name shape value rest) =
      .dec (ofString name) (shapeToHOL shape) (expToHOL value) (progToHOL rest) := by
  rw [progToHOL.eq_def]

theorem progToHOL_store_eq (address value : Exp (BitVec 64)) :
    progToHOL (.store address value) = .store (expToHOL address) (expToHOL value) := by
  rw [progToHOL.eq_def]

theorem progToHOL_seq_eq (first second : Prog (BitVec 64)) :
    progToHOL (.seq first second) = .seq (progToHOL first) (progToHOL second) := by
  rw [progToHOL.eq_def]

theorem progToHOL_assign_eq (kind : VarKind) (name : String) (value : Exp (BitVec 64)) :
    progToHOL (.assign kind name value) = .assign kind (ofString name) (expToHOL value) := by
  rw [progToHOL.eq_def]

theorem progToHOL_ite_eq (condition : Exp (BitVec 64))
    (thenBranch elseBranch : Prog (BitVec 64)) :
    progToHOL (.ite condition thenBranch elseBranch) =
      .ite (expToHOL condition) (progToHOL thenBranch) (progToHOL elseBranch) := by
  rw [progToHOL.eq_def]

theorem progToHOL_while_eq (condition : Exp (BitVec 64)) (body : Prog (BitVec 64)) :
    progToHOL (.while condition body) = .while (expToHOL condition) (progToHOL body) := by
  rw [progToHOL.eq_def]

theorem progToHOL_return_eq (value : Exp (BitVec 64)) :
    progToHOL (.return value) = .return (expToHOL value) := by
  rw [progToHOL.eq_def]

theorem progToHOL_skip_eq : progToHOL (.skip : Prog (BitVec 64)) = .skip := by
  rw [progToHOL.eq_def]

/-- The frozen candidate `htab_new_scratch` starts with the 120-byte table
allocation; the exact continuation is left opaque. -/
theorem candidate_htabNewScratch_allocHead :
    ∃ rest, sourceFunctionBody CandidateGuest.guestFn_htab_new_scratch =
      .decCall (ofString "t") .one (ofString "scratch_alloc")
        [.const (BitVec.ofNat 64 120)] rest := by
  simp only [sourceFunctionBody, CandidateGuest.guestFn_htab_new_scratch, declToHOL,
    funDeclToHOL]
  rw [progToHOL_decCall_eq]
  simp only [shapeToHOL, expToHOL, List.map_cons, List.map_nil]
  exact ⟨_, rfl⟩

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidate_htabNewScratch_allocHead
