import InitECandidate.Runtime.RlpValidationStack
import InitECandidate.Runtime.RlpValidationPop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original stack pop preserves the loop flag and globals. -/
theorem evaluate_rlpValidation_stack_pop_scope {F : Type} (state : PanSemStateFiniteExact 64 F)
    (position stop : BitVec 64) (frontier : Nat) (frame : RlpValidationFrame) (rest : List RlpValidationFrame)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (stopLocal : state.locals.lookup (ofString "end") = some (.val (.word stop)))
    (topLocal : state.locals.lookup (ofString "top") = some (.val (.word frame.record)))
    (valid : RlpValidationStack state.memory frontier (frame :: rest))
    (domain0 : state.memaddrs frame.record) (domain8 : state.memaddrs (frame.record + 8))
    (domain16 : state.memaddrs (frame.record + 16)) :
    ∃ post, evaluateHOLFiniteState state rlpValidationPop = (none,post) ∧
      post.locals.lookup (ofString "go") = state.locals.lookup (ofString "go") ∧ post.globals = state.globals := by
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
    refine ⟨post,run,?_,rfl⟩
    simp [post,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "top" ≠ ofString "go" by decide,show ofString "end" ≠ ofString "go" by decide,
      show ofString "pos" ≠ ofString "go" by decide]

#print axioms evaluate_rlpValidation_stack_pop_scope
end InitECandidate.Runtime
