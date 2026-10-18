import InitECandidate.Runtime.AuthorizationsTailSource
import InitECandidate.Runtime.FourWordStoreMemoryFrame
import InitECandidate.Runtime.ReadOnlyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual final authorization store and increment leave every word
outside the four destination cells unchanged, for every outcome. -/
theorem evaluate_authorization_last_store_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (record first second third fourth watched : BitVec 64)
    (atRecord : state.locals.lookup (ofString "a") = some (.val (.word record)))
    (atValue : state.locals.lookup (ofString "s") =
      some (.rStruct [.val (.word first),.val (.word second),.val (.word third),.val (.word fourth)]))
    (apart0 : watched ≠ record + 88#64) (apart8 : watched ≠ record + 88#64 + 8#64)
    (apart16 : watched ≠ record + 88#64 + 16#64) (apart24 : watched ≠ record + 88#64 + 24#64) :
    (evaluateHOLFiniteState state authorizationLastStore).2.memory watched = state.memory watched := by
  let destination : ExpHOL 64 := .op .add [.var .local (ofString "a"),.const 88]
  let value : ExpHOL 64 := .var .local (ofString "s")
  have addressEval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) destination = some (.val (.word (record + 88#64))) := by
    simp [destination,evalHOLExact,evalListHOLExact,atRecord,wordOpHOL,wordOp,valueIsWord,valueWord]
  have valueEval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) value =
      some (.rStruct [.val (.word first),.val (.word second),.val (.word third),.val (.word fourth)]) := by
    simp [value,evalHOLExact,atValue]
  have frame := evaluate_fourWordStore_memory_frame state destination value (record + 88#64)
    first second third fourth watched addressEval valueEval apart0 apart8 apart16 apart24
  rw [source_authorization_last_store,evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState state (.store destination value) with
  | mk result post =>
    rw [run] at frame
    cases result with
    | none =>
      have kept := evaluate_readOnly_memory (.assign .local (ofString "i")
        (.op .add [.var .local (ofString "i"),.const 1])) (by rfl) post
      exact (congrArg (fun memory => memory watched) kept).trans frame
    | some result => exact frame

#print axioms evaluate_authorization_last_store_frame
end InitECandidate.Runtime
