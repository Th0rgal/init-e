import InitECandidate.Runtime.HashExpressionStep
import InitECandidate.Runtime.HashFinish
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def hashExpressionTail (expression : ExpHOL 64) : ProgHOL 64 :=
  .seq (.assign .local (ofString "w") expression)
    (.seq (.assign .local (ofString "h")
      (.op .xor [.var .local (ofString "h"),.var .local (ofString "w")])) hashFinish)

/-- A readable partial-word load completes the source hash without consuming clocks. -/
theorem evaluate_hashExpressionTail {F : Type} (state : PanSemStateFiniteExact 64 F)
    (expression : ExpHOL 64) (hash oldWord value : BitVec 64)
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash)))
    (wordLocal : state.locals.lookup (ofString "w") = some (.val (.word oldWord)))
    (loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression = some (.val (.word value))) :
    ∃ post, evaluateHOLFiniteState state (hashExpressionTail expression) =
      (some (.returned (.val (.word (hashFinishValue (hash ^^^ value))))),post) ∧
      post.clock = state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have step := evaluate_hashExpressionStep state expression hash oldWord value hashLocal wordLocal loaded
  let middle := setVarHOLFinite (ofString "h") (.val (.word (hash ^^^ value)))
    (setVarHOLFinite (ofString "w") (.val (.word value)) state)
  have binding : middle.locals.lookup (ofString "h") = some (.val (.word (hash ^^^ value))) := by
    simp [middle,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have finish := evaluate_hashFinish middle (hash ^^^ value) binding
  refine ⟨emptyLocalsHOLFinite (setVarHOLFinite (ofString "h") (.val (.word (hashMixSecond (hash ^^^ value))))
    (setVarHOLFinite (ofString "h") (.val (.word (hashMixFirst (hash ^^^ value)))) middle)),
    ?_,?_,?_,?_,?_,?_,?_⟩
  · unfold hashExpressionTail
    rw [← evaluate_seq_assoc]
    change evaluateHOLFiniteState state (.seq (hashExpressionStep expression) hashFinish) = _
    rw [evaluateHOLFiniteState_seq_line780,step]
    exact finish
  all_goals rfl

#print axioms evaluate_hashExpressionTail
end InitECandidate.Runtime
