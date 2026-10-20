import InitECandidate.Runtime.MemoryCeil32ReturnedLower
import InitECandidate.Runtime.MemoryCostPureDeclaration
import InitECandidate.Runtime.PanSingleWordLookup
import InitECandidate.Runtime.VmFn_ceil32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Concrete original ceil32 declaration, exposing its actual rounded value
and resumed source continuation with unchanged memory/globals. -/
theorem memory_ceil32_declaration_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (argument : ExpHOL 64) (tail : ProgHOL 64) (input : BitVec 64) (value : ValueHOL 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [argument]=some [.val (.word input)])
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.decCall name .one (ofString "ceil32") [argument] tail)=(some (.returned value),post)) :
 ∃rounded : BitVec 64,∃bodyPost output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState (setVarHOLFinite name (.val (.word rounded)) {bodyPost with locals:=s.locals}) tail=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} ∧
 input.toNat≤rounded.toNat ∧bodyPost.memory=s.memory ∧bodyPost.globals=s.globals ∧
 bodyPost.code=s.code ∧bodyPost.memaddrs=s.memaddrs ∧bodyPost.be=s.be := by
 have installed : s.code.lookup (ofString "ceil32")=some ([(ofString "v",.one)],sourceFunctionBody Guest.guestFn_ceil32,.one) := by
  rw [code];exact vmLookup_ceil32
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=HolFiniteMapExact.empty.update (ofString "v",.val (.word input))
 have lookup:=pan_single_word_lookup s.code.lookup (ofString "ceil32") (ofString "v") (sourceFunctionBody Guest.guestFn_ceil32) input installed
 obtain ⟨returned,bodyPost,output,bodyRun,checked,tailRun,postEq⟩:=
  evaluate_decCall_checked_returned_exact_scope s post name (ofString "ceil32") .one .one _ _ _ tail callee value args lookup run
 have atV : (callEntryStateHOLFinite s callee).locals.lookup (ofString "v")=some (.val (.word input)) := by
  simp [callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 obtain ⟨rounded,returnedEq,lower⟩:=memory_ceil32_returned_lower (callEntryStateHOLFinite s callee) bodyPost input returned atV code bodyRun
 subst returned
 have frame:=memoryFrame_of_good vmLookup_ceil32 (by decide) (by decide) (callEntryStateHOLFinite s callee) code
 have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) (sourceFunctionBody Guest.guestFn_ceil32)
 rw [bodyRun] at frame metadata
 exact ⟨rounded,bodyPost,output,tailRun,postEq,lower,frame.1,frame.2,metadata.1,metadata.2.1,metadata.2.2.1⟩
#print axioms memory_ceil32_declaration_returned
end InitECandidate.Runtime
