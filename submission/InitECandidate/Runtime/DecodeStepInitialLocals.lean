import InitECandidate.Runtime.DecodeStepParsePrefixReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def decodeStepInitialLocals {F : Type} (s : PanSemStateFiniteExact 64 F) : PanSemStateFiniteExact 64 F :=
  setVarHOLFinite (ofString "e") (.val (.word (0#64)))
    (setVarHOLFinite (ofString "it")
      (.rStruct [.val (.word (0#64)),.val (.word (0#64)),.val (.word (0#64)),.val (.word (0#64))]) s)

theorem source_decode_step_initial_locals : decodeStepAt 0 =
    .dec (ofString "it") (.comb [.one,.one,.one,.one]) (.rstruct [.const 0,.const 0,.const 0,.const 0])
      (.dec (ofString "e") .one (.const 0) (decodeStepAt 2)) := by
  simp only [decodeStepAt,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The two original local declarations consume no source steps, and their
scope restoration does not change the later result, clock or memory effects. -/
theorem decode_step_initial_locals_reaches {F : Type} (s : PanSemStateFiniteExact 64 F) :
    Reaches s (decodeStepAt 0) (fun ready => ready = decodeStepInitialLocals s) 0 (decodeStepAt 2) := by
  refine Or.inl ⟨decodeStepInitialLocals s,rfl,by simp [decodeStepInitialLocals,setVarHOLFinite],
    by simp [decodeStepInitialLocals,setVarHOLFinite],?_⟩
  rw [source_decode_step_initial_locals]
  simp only [evaluateHOLFiniteState_dec_total,evalHOLExact,evalListHOLExact,Option.map_some,
    shapeOfHOLExact,shapeEqHOL]
  simp [Scoped,decodeStepInitialLocals,setVarHOLFinite,emptyLocalsHOLFinite,shapeEqHOL,shapeEqHOL.shapeEqListHOL,shapeOfHOLExact]

#print axioms source_decode_step_initial_locals
#print axioms decode_step_initial_locals_reaches
end InitECandidate.Runtime
