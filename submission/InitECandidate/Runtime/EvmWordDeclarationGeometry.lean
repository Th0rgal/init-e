import InitECandidate.Runtime.EvmSatWordSourceValue
import InitECandidate.Runtime.VmFn_sat_word
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem funding_sat_word_lookup {F : Type} (s : PanSemStateFiniteExact 64 F) (a b c d : BitVec 64)
 (code : s.code=originalRuntimeCode) :
 lookupCodeHOLFinite s.code.lookup (ofString "sat_word") [fundingU256 a b c d]=
 some (sourceFunctionBody Guest.guestFn_sat_word,HolFiniteMapExact.empty.update (ofString "v",fundingU256 a b c d),.one) := by
 apply lookupCodeFinite_of_exact
 have installed:=vmLookup_sat_word
 rw [code]
 simp [lookupCodeHOLExact,installed,fundingU256,shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL]
 funext key
 by_cases same : key=ofString "v"
 · subst key;simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty]
 · simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,same,Ne.symm same]

/-- Actual typed U256 saturation declaration with its exact source value,
resumed scope, and actual read-only callee metadata. -/
theorem funding_sat_word_declaration_geometry {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (argument : ExpHOL 64) (tail : ProgHOL 64) (a b c d : BitVec 64) (value : ValueHOL 64)
 (args : evalListHOLFinite s (h:=fun address=>Classical.propDecidable (s.memaddrs address)) [argument]=some [fundingU256 a b c d])
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.decCall name .one (ofString "sat_word") [argument] tail)=(some (.returned value),post)) :
 ∃bodyPost output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState (setVarHOLFinite name (.val (.word (evmSatWord a b c d))) {bodyPost with locals:=s.locals}) tail=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} ∧
 bodyPost.memory=s.memory ∧bodyPost.globals=s.globals ∧bodyPost.code=s.code ∧bodyPost.memaddrs=s.memaddrs ∧bodyPost.be=s.be := by
 let callee:=HolFiniteMapExact.empty.update (ofString "v",fundingU256 a b c d)
 obtain ⟨returned,bodyPost,output,bodyRun,checked,tailRun,postEq⟩:=evaluate_decCall_checked_returned_exact_scope s post name (ofString "sat_word") .one .one [argument] [fundingU256 a b c d] (sourceFunctionBody Guest.guestFn_sat_word) tail callee value args (funding_sat_word_lookup s a b c d code) run
 have atArgument : (callEntryStateHOLFinite s callee).locals.lookup (ofString "v")=some (fundingU256 a b c d) := by simp [callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have evaluated:=evaluate_source_evm_sat_word (callEntryStateHOLFinite s callee) a b c d atArgument
 have returnedEq : returned=.val (.word (evmSatWord a b c d)):=PanSemResultExact.returned.inj (Option.some.inj (Prod.mk.inj (bodyRun.symm.trans evaluated)).1)
 subst returned
 have frame:=memoryFrame_of_good vmLookup_sat_word (by decide) (by decide) (callEntryStateHOLFinite s callee) code
 have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) (sourceFunctionBody Guest.guestFn_sat_word)
 rw [bodyRun] at frame metadata
 exact ⟨bodyPost,output,tailRun,postEq,frame.1,frame.2,metadata.1,metadata.2.1,metadata.2.2.1⟩

/-- The real zero-test declaration with the same source value and complete
read-only metadata needed by the actual memory-cost entry guard. -/
theorem funding_u256_zero_declaration_geometry {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (argument : ExpHOL 64) (tail : ProgHOL 64) (a b c d : BitVec 64) (value : ValueHOL 64)
 (args : evalListHOLFinite s (h:=fun address=>Classical.propDecidable (s.memaddrs address)) [argument]=some [fundingU256 a b c d])
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.decCall name .one (ofString "u256_is_zero") [argument] tail)=(some (.returned value),post)) :
 ∃bodyPost output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState (setVarHOLFinite name (.val (.word (fundingU256ZeroFlag a b c d))) {bodyPost with locals:=s.locals}) tail=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} ∧
 bodyPost.memory=s.memory ∧bodyPost.globals=s.globals ∧bodyPost.code=s.code ∧bodyPost.memaddrs=s.memaddrs ∧bodyPost.be=s.be := by
 let callee:=HolFiniteMapExact.empty.update (ofString "a",fundingU256 a b c d)
 obtain ⟨returned,bodyPost,output,bodyRun,checked,tailRun,postEq⟩:=evaluate_decCall_checked_returned_exact_scope s post name (ofString "u256_is_zero") .one .one [argument] [fundingU256 a b c d] (sourceFunctionBody Guest.guestFn_u256_is_zero) tail callee value args (funding_single_u256_lookup s a b c d code) run
 have atArgument : (callEntryStateHOLFinite s callee).locals.lookup (ofString "a")=some (fundingU256 a b c d) := by simp [callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have result:=funding_u256_is_zero_result (callEntryStateHOLFinite s callee) a b c d atArgument
 rw [bodyRun] at result
 have returnedEq : returned=.val (.word (fundingU256ZeroFlag a b c d)):=PanSemResultExact.returned.inj (Option.some.inj result)
 subst returned
 have frame:=memoryFrame_of_good vmLookup_u256_is_zero (by decide) (by decide) (callEntryStateHOLFinite s callee) code
 have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) (sourceFunctionBody Guest.guestFn_u256_is_zero)
 rw [bodyRun] at frame metadata
 exact ⟨bodyPost,output,tailRun,postEq,frame.1,frame.2,metadata.1,metadata.2.1,metadata.2.2.1⟩
#print axioms funding_sat_word_lookup
#print axioms funding_sat_word_declaration_geometry
#print axioms funding_u256_zero_declaration_geometry
end InitECandidate.Runtime
