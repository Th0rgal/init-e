import InitECandidate.Runtime.GasFrameExpressions
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Exact physical word-field read through a local pointer in the original
source evaluator. The domain and word value are actual input-state facts. -/
theorem eval_local_word_field {F : Type} (state : PanSemStateFiniteExact 64 F)
 (name : MlS) (pointer offset value : BitVec 64)
 (binding : state.locals.lookup name=some (.val (.word pointer)))
 (domain : state.memaddrs (pointer+offset)) (memory : state.memory (pointer+offset)=.word value) :
 @evalHOLExact 64 F _ state.toExact (fun address=>Classical.propDecidable (state.memaddrs address))
  (.load .one (.op .add [.var .local name,.const offset]))=some (.val (.word value)) := by
 classical
 simp [evalHOLExact,evalListHOLExact,toExact,binding,wordOpHOL,wordOp,valueIsWord,valueWord,
  isWfShapeExactHOL,memLoadHOLExact,domain,memory]

#print axioms eval_local_word_field
end InitECandidate.Runtime
