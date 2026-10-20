import InitECandidate.Runtime.MemoryWordsOfReturnedRange
import InitECandidate.Runtime.VmFn_words_of
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem memory_words_of_declaration_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (argument : ExpHOL 64) (tail : ProgHOL 64) (input : BitVec 64) (value : ValueHOL 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [argument]=some [.val (.word input)])
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.decCall name .one (ofString "words_of") [argument] tail)=(some (.returned value),post)) :
 ∃words : BitVec 64,∃bodyPost output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState (setVarHOLFinite name (.val (.word words)) {bodyPost with locals:=s.locals}) tail=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} ∧
 input.toNat/32≤words.toNat ∧words.toNat<2^59 ∧bodyPost.memory=s.memory ∧bodyPost.globals=s.globals ∧
 bodyPost.code=s.code ∧bodyPost.memaddrs=s.memaddrs ∧bodyPost.be=s.be := by
 have installed : s.code.lookup (ofString "words_of")=some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_words_of,.one) := by
  rw [code];exact vmLookup_words_of
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=HolFiniteMapExact.empty.update (ofString "n",.val (.word input))
 have lookup:=pan_single_word_lookup s.code.lookup (ofString "words_of") (ofString "n") (sourceFunctionBody Guest.guestFn_words_of) input installed
 obtain ⟨returned,bodyPost,output,bodyRun,checked,tailRun,postEq⟩:=
  evaluate_decCall_checked_returned_exact_scope s post name (ofString "words_of") .one .one _ _ _ tail callee value args lookup run
 have atN : (callEntryStateHOLFinite s callee).locals.lookup (ofString "n")=some (.val (.word input)) := by
  simp [callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 obtain ⟨words,returnedEq,lower,ceiling⟩:=memory_words_of_returned_range (callEntryStateHOLFinite s callee) bodyPost input returned atN code bodyRun
 subst returned
 have frame:=memoryFrame_of_good vmLookup_words_of (by decide) (by decide) (callEntryStateHOLFinite s callee) code
 have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) (sourceFunctionBody Guest.guestFn_words_of)
 rw [bodyRun] at frame metadata
 exact ⟨words,bodyPost,output,tailRun,postEq,lower,ceiling,frame.1,frame.2,metadata.1,metadata.2.1,metadata.2.2.1⟩
#print axioms memory_words_of_declaration_returned
end InitECandidate.Runtime
