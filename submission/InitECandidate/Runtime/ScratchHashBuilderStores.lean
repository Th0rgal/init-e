import InitECandidate.Runtime.ScratchHashBuilderContext
import InitECandidate.Runtime.ScratchHashSource
import InitECandidate.Runtime.ReturnedWordStorePrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem ScratchHashBuilderContext.after_context {F : Type} {s : PanSemStateFiniteExact 64 F}
 {table frame pointer : BitVec 64} (valid : ScratchHashBuilderContext s table frame pointer)
 (post : PanSemStateFiniteExact 64 F) (locals : post.locals=s.locals) (globals : post.globals=s.globals) (code : post.code=s.code) :
 ScratchHashBuilderContext post table frame pointer := by
 constructor
 · rw [locals];exact valid.atTable
 · rw [locals];exact valid.atCap
 · rw [locals];exact valid.atStride
 · rw [globals];exact valid.scratchGlobal
 · rw [globals];exact valid.frameGlobal
 · exact valid.ordered
 · exact code.trans valid.code

/-- Strip a real scalar header store from an actual returned path. -/
theorem ScratchHashBuilderContext.store_returned {F : Type} {s : PanSemStateFiniteExact 64 F}
 {table frame pointer : BitVec 64} (valid : ScratchHashBuilderContext s table frame pointer)
 (post : PanSemStateFiniteExact 64 F) (offset word : BitVec 64) (expression : ExpHOL 64) (tail : ProgHOL 64) (value : ValueHOL 64)
 (evaluated : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) expression=some (.val (.word word)))
 (run : evaluateHOLFiniteState s (.seq (.store (scratchHashAddress offset) expression) tail)=(some (.returned value),post)) :
 evaluateHOLFiniteState (sourceWriteWord s (table+offset) word) tail=(some (.returned value),post) := by
 obtain ⟨middle,normal,tailRun⟩:=seq_returned_of_nonreturning_first
  (by intro v;exact evaluate_noDirectReturn _ rfl s v) run
 have address : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (scratchHashAddress offset)=some (.val (.word (table+offset))) := by
  simp [scratchHashAddress,evalHOLExact,evalListHOLExact,valid.atTable,wordOpHOL,wordOp,valueIsWord,valueWord]
 have exactPost:=store_normal_exact s middle _ _ _ _ address evaluated normal
 subst middle
 exact tailRun

theorem ScratchHashBuilderContext.fixed_size_arguments {F : Type} {s : PanSemStateFiniteExact 64 F}
 {table frame pointer : BitVec 64} (valid : ScratchHashBuilderContext s table frame pointer) (factor : BitVec 64) :
 evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [scratchHashSizeExpression (.const factor)]=
 some [.val (.word ((4#64)*factor))] := by
 simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,scratchHashSizeExpression,valid.atCap,panOpHOL,valueIsWord,valueWord]
#print axioms ScratchHashBuilderContext.after_context
#print axioms ScratchHashBuilderContext.store_returned
#print axioms ScratchHashBuilderContext.fixed_size_arguments
end InitECandidate.Runtime
