import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
import InitECandidate.Runtime.PanReturnedPath
import InitECandidate.Runtime.TwoWordValueShape
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- An actual returned scalar declaration-call restores the actual caller's
other locals. This inverts execution; no callee execution is assumed. -/
theorem funding_word_declaration_returned_context {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name function : MlS) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64) (value : ValueHOL 64)
 (run : evaluateHOLFiniteState s (.decCall name .one function arguments tail)=(some (.returned value),post)) :
 ∃word : BitVec 64,∃bodyPost output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState (setVarHOLFinite name (.val (.word word)) {bodyPost with locals:=s.locals}) tail=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} ∧
 bodyPost.code=s.code := by
 obtain ⟨values,body,callee,returnShape,_,_,args,lookup,_⟩:=decCall_returned run
 obtain ⟨returned,bodyPost,output,bodyRun,checked,tailRun,postEq⟩:=evaluate_decCall_checked_returned_exact_scope s post name function .one returnShape arguments values body tail callee value args lookup run
 obtain ⟨word,rfl⟩:=value_word_of_shape_one returned ((shapeEqHOL_eq_true _ _).mp checked.1)
 have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body
 rw [bodyRun] at metadata
 exact ⟨word,bodyPost,output,tailRun,postEq,metadata.1⟩
#print axioms funding_word_declaration_returned_context
end InitECandidate.Runtime
