import InitECandidate.Runtime.RlpValidationNonList
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpValidationFinished : ProgHOL 64 :=
  match rlpValidationStep with | .ite _ body _ => body | _ => .skip

def rlpValidationPop : ProgHOL 64 :=
  match rlpValidationFinished with | .ite _ _ body => body | _ => .skip

theorem source_rlpValidation_step : rlpValidationStep =
    .ite (.cmp .equal (.var .local (ofString "pos")) (.var .local (ofString "end")))
      rlpValidationFinished rlpValidationHeaderCall := by
  simp only [rlpValidationStep,rlpValidationFinished,rlpValidationHeaderCall,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_rlpValidation_finished : rlpValidationFinished =
    .ite (.cmp .equal (.var .local (ofString "top")) (.const 0))
      (.assign .local (ofString "go") (.const 0)) rlpValidationPop := by
  simp only [rlpValidationFinished,rlpValidationPop,rlpValidationStep,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_rlpValidation_pop : rlpValidationPop =
    .seq (.assign .local (ofString "pos") (.load .one (.op .add [.var .local (ofString "top"),.const 0])))
      (.seq (.assign .local (ofString "end") (.load .one (.op .add [.var .local (ofString "top"),.const 8])))
        (.assign .local (ofString "top") (.load .one (.op .add [.var .local (ofString "top"),.const 16])))) := by
  simp only [rlpValidationPop,rlpValidationFinished,rlpValidationStep,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- At the end of the outermost interval the original validator clears its
loop flag without spending source clock or accessing memory. -/
theorem evaluate_rlpValidation_finish_empty {F : Type} (state : PanSemStateFiniteExact 64 F)
    (stop flag : BitVec 64)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word stop)))
    (stopLocal : state.locals.lookup (ofString "end") = some (.val (.word stop)))
    (topLocal : state.locals.lookup (ofString "top") = some (.val (.word 0)))
    (flagLocal : state.locals.lookup (ofString "go") = some (.val (.word flag))) :
    evaluateHOLFiniteState state rlpValidationStep =
      (none,setVarHOLFinite (ofString "go") (.val (.word 0)) state) := by
  rw [source_rlpValidation_step,evaluateHOLFiniteState_ite]
  have finished : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .equal (.var .local (ofString "pos")) (.var .local (ofString "end"))) = some (.val (.word 1)) := by
    simp [evalHOLExact,positionLocal,stopLocal,Compiler.Encoders.Asm.wordCmpHOL]
  rw [finished]
  simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false]
  rw [source_rlpValidation_finished,evaluateHOLFiniteState_ite]
  have empty : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .equal (.var .local (ofString "top")) (.const 0)) = some (.val (.word 1)) := by
    simp [evalHOLExact,topLocal,Compiler.Encoders.Asm.wordCmpHOL]
  rw [empty]
  simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false]
  simp [evaluateHOLFiniteState_assign,evalHOLExact,lookupKvarHOLExact,flagLocal,
    isValidValueHOLExact,setKvarHOLFinite,shapeOfHOLExact,shapeEqHOL]

/-- An unfinished interval executes the original header call directly. -/
theorem evaluate_rlpValidation_step_header {F : Type} (state : PanSemStateFiniteExact 64 F)
    (position stop : BitVec 64)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (stopLocal : state.locals.lookup (ofString "end") = some (.val (.word stop)))
    (different : position ≠ stop) :
    evaluateHOLFiniteState state rlpValidationStep = evaluateHOLFiniteState state rlpValidationHeaderCall := by
  rw [source_rlpValidation_step,evaluateHOLFiniteState_ite]
  simp [evalHOLExact,positionLocal,stopLocal,Compiler.Encoders.Asm.wordCmpHOL,different]

/-- A nonempty stack selects its original three-load pop sequence. -/
theorem evaluate_rlpValidation_finished_pop {F : Type} (state : PanSemStateFiniteExact 64 F)
    (top : BitVec 64)
    (topLocal : state.locals.lookup (ofString "top") = some (.val (.word top))) (nonzero : top ≠ 0) :
    evaluateHOLFiniteState state rlpValidationFinished = evaluateHOLFiniteState state rlpValidationPop := by
  rw [source_rlpValidation_finished,evaluateHOLFiniteState_ite]
  have notZero : top ≠ BitVec.ofNat 64 0 := nonzero
  simp [evalHOLExact,topLocal,Compiler.Encoders.Asm.wordCmpHOL,notZero]

#print axioms evaluate_rlpValidation_step_header
#print axioms evaluate_rlpValidation_finished_pop
#print axioms evaluate_rlpValidation_finish_empty
end InitECandidate.Runtime
