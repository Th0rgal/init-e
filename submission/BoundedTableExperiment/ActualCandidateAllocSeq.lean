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

namespace BoundedTableExperiment

open InitECandidate.Runtime
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

/-- Arguments of the direct calls in a program, in execution order. -/
def callArgs : ProgHOL 64 → List (List (ExpHOL 64))
  | .decCall _ _ _ args body => args :: callArgs body
  | .call _ _ args => [args]
  | .seq a b => callArgs a ++ callArgs b
  | .dec _ _ _ body => callArgs body
  | .ite _ a b => callArgs a ++ callArgs b
  | .while _ body => callArgs body
  | _ => []

/-- The frozen candidate allocation requests, with the 120-byte header first
and `nodes = (cap>>1)*24` immediately before `path = key_len*64`. -/
theorem candidate_htabNewScratch_args :
    callArgs (sourceFunctionBody CandidateGuest.guestFn_htab_new_scratch) =
      [ [.const (BitVec.ofNat 64 120)],
        [.panop .mul [.var .local (ofString "cap"), .var .local (ofString "stride")]],
        [.panop .mul [.var .local (ofString "cap"), .const (BitVec.ofNat 64 8)]],
        [.panop .mul [.var .local (ofString "cap"), .const (BitVec.ofNat 64 8)]],
        [.panop .mul [.var .local (ofString "cap"), .const (BitVec.ofNat 64 8)]],
        [.panop .mul [.shift .asr (.var .local (ofString "cap")) (.const (BitVec.ofNat 64 1)),
          .const (BitVec.ofNat 64 24)]],
        [.panop .mul [.var .local (ofString "key_len"), .const (BitVec.ofNat 64 64)]] ] := by
  simp [sourceFunctionBody, CandidateGuest.guestFn_htab_new_scratch, declToHOL,
    funDeclToHOL, progToHOL, expToHOL, callArgs]

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidate_htabNewScratch_args
