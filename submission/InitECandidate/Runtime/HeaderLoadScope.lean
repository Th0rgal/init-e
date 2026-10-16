import InitECandidate.Runtime.HashInsertCountTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem evaluate_header_load_scope {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name base : MlS) (pointer offset value : BitVec 64) (continuation : ProgHOL 64)
    (binding : state.locals.lookup base = some (.val (.word pointer)))
    (domain : state.memaddrs (pointer + offset)) (cell : state.memory (pointer + offset) = .word value) :
    evaluateHOLFiniteState state (.dec name .one (.load .one (hashLocalAddress base offset)) continuation) =
      (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word value)) state) continuation;
       (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name))})) := by
  have loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (hashLocalAddress base offset)) = some (.val (.word value)) := by
    simp only [evalHOLExact,isWfShapeExactHOL]
    rw [eval_hashLocalAddress state base pointer offset binding]
    simp [memLoadHOLExact,domain,cell]
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [loaded]
  dsimp only
  have shapeOk : shapeEqHOL .one (shapeOfHOLExact (.val (.word value))) = true := by
    simp [shapeOfHOLExact,shapeEqHOL]
  rw [if_pos shapeOk]

#print axioms evaluate_header_load_scope
end InitECandidate.Runtime
