import InitECandidate.Runtime.FundingWordDeclarationReturnedContext
import InitECandidate.Runtime.GlobalKeepAllProgram
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Real scalar declaration-call inversion for the statically verified original
read-only closure. Static goodMem/goodGA booleans carry no runtime oracle. -/
theorem memory_cost_pure_declaration_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name function : MlS) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64) (value : ValueHOL 64)
 (code : s.code=originalRuntimeCode) (pureMemory : goodMem function=true) (pureGlobals : goodGA function=true)
 (run : evaluateHOLFiniteState s (.decCall name .one function arguments tail)=(some (.returned value),post)) :
 ∃word : BitVec 64,∃bodyPost output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState (setVarHOLFinite name (.val (.word word)) {bodyPost with locals:=s.locals}) tail=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} ∧
 bodyPost.memory=s.memory ∧bodyPost.globals=s.globals ∧bodyPost.code=s.code ∧
 bodyPost.memaddrs=s.memaddrs ∧bodyPost.be=s.be := by
 obtain ⟨values,body,callee,returnShape,_,_,args,lookup,_⟩:=decCall_returned run
 obtain ⟨returned,bodyPost,output,bodyRun,checked,tailRun,postEq⟩:=evaluate_decCall_checked_returned_exact_scope s post name function .one returnShape arguments values body tail callee value args lookup run
 obtain ⟨word,rfl⟩:=value_word_of_shape_one returned ((shapeEqHOL_eq_true _ _).mp checked.1)
 obtain ⟨params,rs,installed⟩:=lookupCode_installed lookup
 rw [code] at installed
 have frame:=memoryFrame_of_good installed pureMemory pureGlobals (callEntryStateHOLFinite s callee) code
 have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body
 rw [bodyRun] at frame metadata
 exact ⟨word,bodyPost,output,tailRun,postEq,frame.1,frame.2,metadata.1,metadata.2.1,metadata.2.2.1⟩
#print axioms memory_cost_pure_declaration_returned
end InitECandidate.Runtime
