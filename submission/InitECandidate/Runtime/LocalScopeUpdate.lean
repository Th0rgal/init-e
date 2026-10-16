import InitECandidate.Runtime.LocalScopeRestore
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A scope restores its previous local even if its body changed that local's
value, as an exception handler does to err. Other local bindings are preserved. -/
theorem evaluate_scoped_body_updated_local {width : Nat} [NeZero width] {F : Type}
    (state post : PanSemStateFiniteExact width F) (name : MlS) (shape : ShapeHOL)
    (initializer : ExpHOL width) (body : ProgHOL width) (initialValue finalValue : ValueHOL width)
    (result : Option (PanSemResultExact width))
    (initial : @evalHOLExact width F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) initializer = some initialValue)
    (shapeOk : shapeEqHOL shape (shapeOfHOLExact initialValue) = true)
    (run : evaluateHOLFiniteState (setVarHOLFinite name initialValue state) body = (result,post))
    (updated : post.locals = (setVarHOLFinite name finalValue state).locals) :
    evaluateHOLFiniteState state (.dec name shape initializer body) = (result,{post with locals := state.locals}) := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [initial]
  dsimp only
  rw [if_pos shapeOk,run]
  rw [restore_body_locals state post name finalValue updated]

#print axioms evaluate_scoped_body_updated_local
end InitECandidate.Runtime
