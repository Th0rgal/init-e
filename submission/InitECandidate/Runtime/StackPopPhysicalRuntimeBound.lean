import InitECandidate.Runtime.EvmStackPopDeclarationPhysicalContext
import InitECandidate.Runtime.RlpPutU256CheckedDeclaration
import InitECandidate.Runtime.VmFn_stack_pop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Checked actual pop plus a concrete physical continuation. The callee bound
and returned physical/funding frame are derived from the original source. -/
theorem runBounded_stack_pop_physical_declaration {F : Type}
 (s : PanSemStateFiniteExact 64 F) (upper : Nat)
 (current : InterpreterFundingFrame) (ancestors : List InterpreterFundingFrame)
 (layout : InterpreterFundingLayout s current.address.toNat upper (current::ancestors))
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s current.address words)
 (name : MlS) (tail : ProgHOL 64) (cost : Nat)
 (code : s.code=originalRuntimeCode) (budget : 1+cost≤s.clock)
 (resume : ∀(a b c d : BitVec 64) (ready : PanSemStateFiniteExact 64 F),
  ready.locals.lookup name=some (fundingU256 a b c d) →
  (∀key, key≠name → ready.locals.lookup key=s.locals.lookup key) →
  0<words.stackSize.toNat →
  EvmMemoryOperandAt ready current.address {words with stackSize:=words.stackSize-1} →
  InterpreterFundingLayout ready current.address.toNat upper (current::ancestors) →
  ready.code=originalRuntimeCode →cost≤ready.clock →RunBounded ready tail cost) :
 RunBounded s (.decCall name (.comb [.one,.one,.one,.one]) (ofString "stack_pop") [] tail) (1+cost) := by
 apply runBounded_checked_declaration s name (ofString "stack_pop") (.comb [.one,.one,.one,.one]) [] tail 0 cost (by omega)
 intro values body callee returnShape args lookup
 have valuesEmpty : values=[]:=Option.some.inj args.symm
 subst values
 have installed : s.code.lookup (ofString "stack_pop")=some ([],sourceFunctionBody Guest.guestFn_stack_pop,.comb [.one,.one,.one,.one]) := by rw [code];exact vmLookup_stack_pop
 have expected:=pan_no_args_shape_lookup s.code.lookup (ofString "stack_pop") (sourceFunctionBody Guest.guestFn_stack_pop) (.comb [.one,.one,.one,.one]) installed
 have equal:=Option.some.inj (lookup.symm.trans expected)
 obtain ⟨rfl,rfl,rfl⟩:=Prod.mk.inj equal
 constructor
 · exact ProgBounded.bodies_of_fun vmBound_stack_pop s code (by omega) [] _ _ _ expected
 · intro value post ran checked remaining
   have pair := checked
   simp only [Bool.and_eq_true] at pair
   obtain ⟨a,b,c,d,equal⟩:=value_four_words_of_checked_shape value pair.1
   subst value
   let entry:=callEntryStateHOLFinite s HolFiniteMapExact.empty
   have entryValid : EvmMemoryOperandAt entry current.address words:=valid.after_context rfl rfl rfl
   obtain ⟨positive,physical,upperFrame,globals,domain,endian,installedKept⟩:=stack_pop_returned_physical_context entry post current.address words entryValid (fundingU256 a b c d) ran
   obtain ⟨_,memory,_,_,_,_,_⟩:=stack_pop_body_returned_frame entry post current.address words.stackSize (fundingU256 a b c d) valid.ev (valid.headerDomain 16 (by simp)) valid.stackSize ran
   let ready:=setVarHOLFinite name (fundingU256 a b c d) {post with locals:=s.locals}
   have readyValid : EvmMemoryOperandAt ready current.address {words with stackSize:=words.stackSize-1}:=physical.after_context rfl rfl rfl
   have paid : InterpreterFundingLayout ready current.address.toNat upper (current::ancestors):=interpreter_funding_after_stack_counter s ready upper current ancestors layout (words.stackSize-1) memory domain
   exact resume a b c d ready (by simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) (by intro key different; simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different]) positive readyValid paid (installedKept.trans code) remaining
#print axioms runBounded_stack_pop_physical_declaration
end InitECandidate.Runtime
