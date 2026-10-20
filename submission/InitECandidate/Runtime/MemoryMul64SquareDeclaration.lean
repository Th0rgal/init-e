import InitECandidate.Runtime.MemoryMul64SchoolbookReturned
import InitECandidate.Runtime.MemoryCostPureDeclaration
import InitECandidate.Runtime.VmFn_mul64x64
import InitECandidate.Runtime.PanTwoWordResultLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem memory_mul64_square_declaration_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64) (input : BitVec 64) (value : ValueHOL 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some [.val (.word input),.val (.word input)])
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.decCall name (.comb [.one,.one]) (ofString "mul64x64") arguments tail)=(some (.returned value),post)) :
 ∃bodyPost output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState (setVarHOLFinite name (.rStruct [.val (.word (memoryMul64Schoolbook input input).1),.val (.word (memoryMul64Schoolbook input input).2)]) {bodyPost with locals:=s.locals}) tail=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} ∧
 bodyPost.memory=s.memory ∧bodyPost.globals=s.globals ∧bodyPost.code=s.code ∧bodyPost.memaddrs=s.memaddrs ∧bodyPost.be=s.be := by
 have installed : s.code.lookup (ofString "mul64x64")=some ([(ofString "a",.one),(ofString "b",.one)],sourceFunctionBody Guest.guestFn_mul64x64,.comb [.one,.one]) := by
  rw [code];exact vmLookup_mul64x64
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=(HolFiniteMapExact.empty.update (ofString "a",.val (.word input))).update (ofString "b",.val (.word input))
 have lookup:=pan_two_word_result_lookup s.code.lookup (ofString "mul64x64") (ofString "a") (ofString "b") (sourceFunctionBody Guest.guestFn_mul64x64) input input (.comb [.one,.one]) (by decide) installed
 obtain ⟨returned,bodyPost,output,bodyRun,checked,tailRun,postEq⟩:=
  evaluate_decCall_checked_returned_exact_scope s post name (ofString "mul64x64") (.comb [.one,.one]) (.comb [.one,.one]) _ _ _ tail callee value args lookup run
 have atA : (callEntryStateHOLFinite s callee).locals.lookup (ofString "a")=some (.val (.word input)) := by
  simp (config:={decide:=true}) [callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have atB : (callEntryStateHOLFinite s callee).locals.lookup (ofString "b")=some (.val (.word input)) := by
  simp [callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have returnedEq:=memory_mul64_schoolbook_returned (callEntryStateHOLFinite s callee) bodyPost input input returned atA atB bodyRun
 subst returned
 have frame:=memoryFrame_of_good vmLookup_mul64x64 (by decide) (by decide) (callEntryStateHOLFinite s callee) code
 have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) (sourceFunctionBody Guest.guestFn_mul64x64)
 rw [bodyRun] at frame metadata
 exact ⟨bodyPost,output,tailRun,postEq,frame.1,frame.2,metadata.1,metadata.2.1,metadata.2.2.1⟩
#print axioms memory_mul64_square_declaration_returned
end InitECandidate.Runtime
