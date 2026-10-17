import InitECandidate.Runtime.RlpValidationStack
import InitECandidate.Runtime.RlpValidationPop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Popping the original validator stack obtains the three saved words from
the linked-stack certificate and retains the complete remaining stack. -/
theorem evaluate_rlpValidation_stack_pop {F : Type} (state : PanSemStateFiniteExact 64 F)
    (position stop : BitVec 64) (frontier : Nat) (frame : RlpValidationFrame) (rest : List RlpValidationFrame)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (stopLocal : state.locals.lookup (ofString "end") = some (.val (.word stop)))
    (topLocal : state.locals.lookup (ofString "top") = some (.val (.word frame.record)))
    (valid : RlpValidationStack state.memory frontier (frame :: rest))
    (domain0 : state.memaddrs frame.record) (domain8 : state.memaddrs (frame.record + 8))
    (domain16 : state.memaddrs (frame.record + 16)) :
    ∃ post, evaluateHOLFiniteState state rlpValidationPop = (none,post) ∧
      post.locals.lookup (ofString "pos") = some (.val (.word frame.resume)) ∧
      post.locals.lookup (ofString "end") = some (.val (.word frame.stop)) ∧
      post.locals.lookup (ofString "top") = some (.val (.word (rlpValidationStackTop rest))) ∧
      RlpValidationStack post.memory frontier rest ∧ post.clock = state.clock ∧ post.memory = state.memory := by
  classical
  cases valid with
  | cons _ _ nonzero above bounded savedPosition savedStop savedTop tail =>
    change state.memaddrs (frame.record + 8#64) at domain8
    change state.memaddrs (frame.record + 16#64) at domain16
    change state.memory (frame.record + 8#64) = .word frame.stop at savedStop
    change state.memory (frame.record + 16#64) = .word (rlpValidationStackTop rest) at savedTop
    have readPosition : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) (.load .one (.const (frame.record + 0))) =
        some (.val (.word frame.resume)) := by
      simp [evalHOLExact,isWfShapeExactHOL,memLoadHOLExact,domain0,savedPosition]
    have readStop : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) (.load .one (.const (frame.record + 8))) =
        some (.val (.word frame.stop)) := by
      simp [evalHOLExact,isWfShapeExactHOL,memLoadHOLExact,domain8,savedStop]
    have readTop : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) (.load .one (.const (frame.record + 16))) =
        some (.val (.word (rlpValidationStackTop rest))) := by
      simp [evalHOLExact,isWfShapeExactHOL,memLoadHOLExact,domain16,savedTop]
    have run := evaluate_rlpValidation_pop state position stop frame.record frame.resume frame.stop
      (rlpValidationStackTop rest) positionLocal stopLocal topLocal readPosition readStop readTop
    let post := setVarHOLFinite (ofString "top") (.val (.word (rlpValidationStackTop rest)))
      (setVarHOLFinite (ofString "end") (.val (.word frame.stop))
        (setVarHOLFinite (ofString "pos") (.val (.word frame.resume)) state))
    have fields := rlpValidation_pop_post state frame.resume frame.stop (rlpValidationStackTop rest)
    exact ⟨post,run,fields.1,fields.2.1,fields.2.2.1,tail,fields.2.2.2.1,fields.2.2.2.2.1⟩

/-- A finished interval with a certified nonempty stack executes its pop. -/
theorem evaluate_rlpValidation_step_stack_pop {F : Type} (state : PanSemStateFiniteExact 64 F)
    (stop : BitVec 64) (frontier : Nat) (frame : RlpValidationFrame) (rest : List RlpValidationFrame)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word stop)))
    (stopLocal : state.locals.lookup (ofString "end") = some (.val (.word stop)))
    (topLocal : state.locals.lookup (ofString "top") = some (.val (.word frame.record)))
    (valid : RlpValidationStack state.memory frontier (frame :: rest)) :
    evaluateHOLFiniteState state rlpValidationStep = evaluateHOLFiniteState state rlpValidationPop := by
  have nonzero : frame.record ≠ 0 := by
    cases valid with | cons _ _ nonzero _ _ _ _ _ _ => exact nonzero
  rw [source_rlpValidation_step,evaluateHOLFiniteState_ite]
  have guard : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .equal (.var .local (ofString "pos")) (.var .local (ofString "end"))) = some (.val (.word 1)) := by
    simp [evalHOLExact,positionLocal,stopLocal,Compiler.Encoders.Asm.wordCmpHOL]
  rw [guard]
  simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false]
  exact evaluate_rlpValidation_finished_pop state frame.record topLocal nonzero

#print axioms evaluate_rlpValidation_step_stack_pop
#print axioms evaluate_rlpValidation_stack_pop
end InitECandidate.Runtime
