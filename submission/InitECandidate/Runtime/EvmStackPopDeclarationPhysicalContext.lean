import InitECandidate.Runtime.EvmStackPopPhysicalContext
import InitECandidate.Runtime.InterpreterFundingStackPop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Actual checked pop declaration resumes its real caller with typed limbs,
updated physical operand state and all live funding. No callee frame is assumed. -/
theorem stack_pop_declaration_returned_physical_context {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (upper : Nat)
 (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s current.address words)
 (name : MlS) (tail : ProgHOL 64) (value : ValueHOL 64)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.decCall name (.comb [.one,.one,.one,.one]) (ofString "stack_pop") [] tail)=(some (.returned value),post)) :
 ∃a b c d : BitVec 64,∃bodyPost output : PanSemStateFiniteExact 64 F,
 let ready:=setVarHOLFinite name (fundingU256 a b c d) {bodyPost with locals:=s.locals}
 evaluateHOLFiniteState ready tail=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} ∧
 0<words.stackSize.toNat ∧
 EvmMemoryOperandAt ready current.address {words with stackSize:=words.stackSize-1} ∧
 InterpreterFundingLayout ready current.address.toNat upper (current::ancestors) ∧
 ready.globals=s.globals ∧ready.memaddrs=s.memaddrs ∧ready.be=s.be ∧ready.code=s.code ∧
 (∀watched : BitVec 64,watched≠current.address+16→ ready.memory watched=s.memory watched) := by
 have installed : s.code.lookup (ofString "stack_pop")=some ([],sourceFunctionBody Guest.guestFn_stack_pop,.comb [.one,.one,.one,.one]) := by rw [code];exact vmLookup_stack_pop
 have lookup:=pan_no_args_shape_lookup s.code.lookup (ofString "stack_pop") (sourceFunctionBody Guest.guestFn_stack_pop) (.comb [.one,.one,.one,.one]) installed
 have args : evalListHOLFinite s (h:=fun x=>Classical.propDecidable (s.memaddrs x)) []=some []:=rfl
 obtain ⟨returned,bodyPost,output,bodyRun,checked,tailRun,scope⟩:=evaluate_decCall_checked_returned_exact_scope s post name (ofString "stack_pop") (.comb [.one,.one,.one,.one]) (.comb [.one,.one,.one,.one]) [] [] _ tail HolFiniteMapExact.empty value args lookup run
 obtain ⟨a,b,c,d,equal⟩:=value_four_words_of_checked_shape returned checked.1
 subst returned
 let entry:=callEntryStateHOLFinite s HolFiniteMapExact.empty
 have entryValid : EvmMemoryOperandAt entry current.address words:=valid.after_context rfl rfl rfl
 obtain ⟨positive,physical,upperFrame,globals,domain,endian,installedKept⟩:=stack_pop_returned_physical_context entry bodyPost current.address words entryValid (fundingU256 a b c d) bodyRun
 obtain ⟨_,memory,_,_,_,_,_⟩:=stack_pop_body_returned_frame entry bodyPost current.address words.stackSize (fundingU256 a b c d) valid.ev (valid.headerDomain 16 (by simp)) valid.stackSize bodyRun
 let ready:=setVarHOLFinite name (fundingU256 a b c d) {bodyPost with locals:=s.locals}
 have readyValid : EvmMemoryOperandAt ready current.address {words with stackSize:=words.stackSize-1}:=physical.after_context rfl rfl rfl
 have paid : InterpreterFundingLayout ready current.address.toNat upper (current::ancestors):=interpreter_funding_after_stack_counter s ready upper current ancestors layout (words.stackSize-1) memory domain
 exact ⟨a,b,c,d,bodyPost,output,tailRun,scope,positive,readyValid,paid,globals,domain,endian,installedKept,upperFrame⟩
#print axioms stack_pop_declaration_returned_physical_context
end InitECandidate.Runtime
