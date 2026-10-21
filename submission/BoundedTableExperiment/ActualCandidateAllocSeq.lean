import CandidateGuestAst
import InitECandidate.Runtime.SourceClock

namespace BoundedTableExperiment

open InitECandidate.Runtime
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 2000000

/-- Names of the direct callees in a program, in execution order; nested
bodies are traversed but not executed. -/
def callNames : ProgHOL 64 → List MlS
  | .decCall _ _ f _ body => f :: callNames body
  | .call _ f _ => [f]
  | .seq a b => callNames a ++ callNames b
  | .dec _ _ _ body => callNames body
  | .ite _ a b => callNames a ++ callNames b
  | .while _ body => callNames body
  | _ => []

/-- The frozen candidate `htab_new_scratch` calls exactly these functions in
this order; notably `nodes` is allocated immediately before `path`. -/
theorem candidate_htabNewScratch_calls :
    callNames (sourceFunctionBody CandidateGuest.guestFn_htab_new_scratch) =
      [ofString "scratch_alloc", ofString "scratch_alloc",
       ofString "scratch_alloc", ofString "scratch_alloc",
       ofString "scratch_alloc", ofString "scratch_alloc",
       ofString "scratch_alloc"] := by
  simp [sourceFunctionBody, CandidateGuest.guestFn_htab_new_scratch, declToHOL,
    funDeclToHOL, progToHOL, callNames]

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidate_htabNewScratch_calls
