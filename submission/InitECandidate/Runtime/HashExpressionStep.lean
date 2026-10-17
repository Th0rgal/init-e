import InitECandidate.Runtime.HashWordStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Hash mixing after an evaluated source load, including partial-word tails. -/
def hashExpressionStep (expression : ExpHOL 64) : ProgHOL 64 :=
  .seq (.assign .local (ofString "w") expression)
    (.assign .local (ofString "h") (.op .xor [.var .local (ofString "h"),.var .local (ofString "w")]))

theorem evaluate_hashExpressionStep {F : Type} (state : PanSemStateFiniteExact 64 F)
    (expression : ExpHOL 64) (hash oldWord value : BitVec 64)
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash)))
    (wordLocal : state.locals.lookup (ofString "w") = some (.val (.word oldWord)))
    (loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression = some (.val (.word value))) :
    evaluateHOLFiniteState state (hashExpressionStep expression) =
      (none,setVarHOLFinite (ofString "h") (.val (.word (hash ^^^ value)))
        (setVarHOLFinite (ofString "w") (.val (.word value)) state)) := by
  have first := evaluate_local_word_assignment state (ofString "w") _ oldWord value wordLocal loaded
  let middle := setVarHOLFinite (ofString "w") (.val (.word value)) state
  have wh : ofString "w" ≠ ofString "h" := by decide
  have h : middle.locals.lookup (ofString "h") = some (.val (.word hash)) := by
    simpa [middle,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,wh] using hashLocal
  have w : middle.locals.lookup (ofString "w") = some (.val (.word value)) := by
    simp [middle,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have mixed : @evalHOLExact 64 F _ middle.toExact
      (fun address => Classical.propDecidable (middle.memaddrs address))
      (.op .xor [.var .local (ofString "h"),.var .local (ofString "w")]) =
        some (.val (.word (hash ^^^ value))) := by
    simp [evalHOLExact,evalListHOLExact,h,w,wordOpHOL,wordOp,valueIsWord,valueWord]
  have second := evaluate_local_word_assignment middle (ofString "h") _ hash (hash ^^^ value) h mixed
  unfold hashExpressionStep
  rw [evaluateHOLFiniteState_seq_line780,first]
  exact second

#print axioms evaluate_hashExpressionStep
end InitECandidate.Runtime
