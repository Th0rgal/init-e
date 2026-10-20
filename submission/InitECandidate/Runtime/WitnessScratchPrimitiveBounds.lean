import InitECandidate.Runtime.ProgBounded
import InitECandidate.Runtime.ScratchMarkCall
import InitECandidate.Runtime.ScratchReleaseCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
 theorem scratch_mark_fun_bounded : FunBounded (ofString "scratch_mark") 0 := by
  refine ⟨[],sourceFunctionBody Guest.guestFn_scratch_mark,.one,originalRuntimeCode_scratchMark_lookup,?_⟩
  apply ProgBounded.straight
  rw [source_scratchMark_body];rfl
 theorem scratch_release_fun_bounded : FunBounded (ofString "scratch_release") 0 := by
  refine ⟨[(ofString "m",.one)],sourceFunctionBody Guest.guestFn_scratch_release,.one,originalRuntimeCode_scratchRelease_lookup,?_⟩
  apply ProgBounded.straight
  rw [source_scratch_release];rfl
#print axioms scratch_mark_fun_bounded
#print axioms scratch_release_fun_bounded
end InitECandidate.Runtime
