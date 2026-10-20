import InitECandidate.Runtime.U256ZeroFundingValue
import InitECandidate.Runtime.EvmStackPopReturnedFrame
import InitECandidate.Runtime.PanNoArgsShapeLookup
import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
import InitECandidate.Runtime.FourWordValueShape
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Actual installed stack_pop declaration supplies four real word limbs and
its exact one-counter frame, with the original caller's continuation/scope. -/
theorem stack_pop_declaration_returned_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (tail : ProgHOL 64) (frame index : BitVec 64) (value : ValueHOL 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (domain : s.memaddrs (frame+16)) (indexAt : s.memory (frame+16)=.word index)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.decCall name (.comb [.one,.one,.one,.one]) (ofString "stack_pop") [] tail)=(some (.returned value),post)) :
 ∃a b c d : BitVec 64,∃bodyPost output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState (setVarHOLFinite name (fundingU256 a b c d) {bodyPost with locals:=s.locals}) tail=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} ∧
 0<index.toNat ∧bodyPost.memory=(sourceWriteWord s (frame+16) (index-1)).memory ∧bodyPost.globals=s.globals ∧bodyPost.clock=s.clock-1 ∧
 bodyPost.memaddrs=s.memaddrs ∧bodyPost.be=s.be ∧bodyPost.code=s.code := by
 have installed : s.code.lookup (ofString "stack_pop")=some ([],sourceFunctionBody Guest.guestFn_stack_pop,.comb [.one,.one,.one,.one]) := by
  rw [code];exact vmLookup_stack_pop
 have lookup:=pan_no_args_shape_lookup s.code.lookup (ofString "stack_pop") (sourceFunctionBody Guest.guestFn_stack_pop) (.comb [.one,.one,.one,.one]) installed
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) []=some []:=by rfl
 obtain ⟨returned,bodyPost,output,bodyRun,checked,tailRun,scope⟩:=evaluate_decCall_checked_returned_exact_scope s post name (ofString "stack_pop") (.comb [.one,.one,.one,.one]) (.comb [.one,.one,.one,.one]) [] [] _ tail HolFiniteMapExact.empty value args lookup run
 obtain ⟨a,b,c,d,returnedEq⟩:=value_four_words_of_checked_shape returned checked.1
 subst returned
 obtain ⟨positive,memory,globals,clock,domainKept,endian,installedKept⟩:=stack_pop_body_returned_frame (callEntryStateHOLFinite s HolFiniteMapExact.empty) bodyPost frame index (fundingU256 a b c d) atFrame domain indexAt bodyRun
 exact ⟨a,b,c,d,bodyPost,output,tailRun,scope,positive,memory,globals,clock,domainKept,endian,installedKept⟩
#print axioms stack_pop_declaration_returned_frame
end InitECandidate.Runtime
