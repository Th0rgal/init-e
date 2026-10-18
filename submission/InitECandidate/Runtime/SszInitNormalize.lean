import InitECandidate.Runtime.SszInitSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

private theorem sequence_tail_congr {F : Type} (state : PanSemStateFiniteExact 64 F)
    (first second third : ProgHOL 64)
    (same : ∀ current : PanSemStateFiniteExact 64 F, evaluateHOLFiniteState current second = evaluateHOLFiniteState current third) :
    evaluateHOLFiniteState state (.seq first second) = evaluateHOLFiniteState state (.seq first third) := by
  simp only [evaluateHOLFiniteState_seq_line780]
  simp_rw [same]

/-- Normalize the literal multiplication in the allocation argument only
after checking expression semantics; the challenge source is unchanged. -/
theorem evaluate_sszInit_normalized {F : Type} (state : PanSemStateFiniteExact 64 F)
    (zero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word 0))) :
    evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_ssz_init) =
      evaluateHOLFiniteState state sszInitNormalizedSetup := by
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.cmp .notEqual (.var .global (ofString "zero_hashes")) (.const 0)) = some (.val (.word 0)) := by
    simp [evalHOLExact,zero,Compiler.Encoders.Asm.wordCmpHOL]
  rw [source_sszInit_body,evaluateHOLFiniteState_seq_line780]
  simp only [evaluateHOLFiniteState_ite,condition,if_true,evaluateHOLFiniteState_skip]
  simp only [sszInitActualSetup,sszInitNormalizedSetup,sszInitAllocations,globalAllocationProgram]
  apply sequence_tail_congr
  intro middle
  apply sequence_tail_congr
  intro ready
  have args : evalListHOLFinite ready (h := fun a => Classical.propDecidable (ready.memaddrs a))
      [.panop .mul [.const 64,.const 32]] =
        evalListHOLFinite ready (h := fun a => Classical.propDecidable (ready.memaddrs a)) [.const 2048] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,panOpHOL,valueIsWord,valueWord]
  simp only [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_call]
  rw [args]

#print axioms evaluate_sszInit_normalized
end InitECandidate.Runtime
