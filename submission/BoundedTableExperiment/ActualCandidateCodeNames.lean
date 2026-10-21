import CandidateGuestAst
import InitECandidate.Runtime.OriginalRuntimeCode

namespace BoundedTableExperiment

open InitECandidate.Runtime
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

/-- Function names in a declaration list, skipping globals; this is the first
component of `functionsHOL`. -/
def functionNames : List (DeclHOL 64) → List MlS
  | [] => []
  | .function declaration :: rest => declaration.name :: functionNames rest
  | _ :: rest => functionNames rest

/-- Names of `functionsHOL`. -/
theorem functionsHOL_names (declarations : List (DeclHOL 64)) :
    (functionsHOL declarations).map Prod.fst = functionNames declarations := by
  induction declarations with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration with
      | function d => simp [functionsHOL, functionNames, ih]
      | decl shape name value => simp [functionsHOL, functionNames, ih]
      | exnDecl name shape => simp [functionsHOL, functionNames, ih]
      | name name fields => simp [functionsHOL, functionNames, ih]

/-- Key-absence over `functionsHOL` reduces to key-absence over names. -/
theorem functionsHOL_all (declarations : List (DeclHOL 64)) (key : MlS) :
    (functionsHOL declarations).all (fun entry => !(key == entry.1)) =
      (functionNames declarations).all (fun name => !(key == name)) := by
  have h := congrArg (fun l => l.all (fun entry => !(key == entry))) (functionsHOL_names declarations)
  simp only [List.all_map] at h
  exact h

end BoundedTableExperiment

#print axioms BoundedTableExperiment.functionsHOL_names
#print axioms BoundedTableExperiment.functionsHOL_all
