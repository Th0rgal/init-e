import InitECandidate.Runtime.StackPushNoGrowthCallPhysicalContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
/-- The real word push helper: one real four-limb struct push of
`[w,0,0,0]` and a zero return. -/
def stackPushWordBody : ProgHOL 64:=sourceFunctionBody Guest.guestFn_stack_push_word

def stackPushWordValue : ExpHOL 64:=.rstruct [.var .local (ofString "w"),.const 0,.const 0,.const 0]

theorem source_stack_push_word :
 stackPushWordBody=.seq (.call (some (none,none)) (ofString "stack_push") [stackPushWordValue]) (.return (.const 0)) := by
 simp only [stackPushWordBody,stackPushWordValue,sourceFunctionBody_eq_structural];rfl
private theorem push_word_args {F : Type} (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
 (atW : s.locals.lookup (ofString "w")=some (.val (.word w))) :
 evalListHOLFinite s (h:=fun x=>Classical.propDecidable (s.memaddrs x)) [stackPushWordValue]=some [fundingU256 w 0 0 0] := by
 simp [stackPushWordValue,fundingU256,evalListHOLFinite,evalListHOLExact,evalHOLExact,atW]
/-- The real word push helper closes a concrete operand state. -/
theorem stack_push_word_returned_physical_context {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (frame : BitVec 64)
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s frame words)
 (w : BitVec 64) (value : ValueHOL 64)
 (atW : s.locals.lookup (ofString "w")=some (.val (.word w)))
 (inside : words.stackSize.toNat<words.stackCapacity.toNat)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s stackPushWordBody=(some (.returned value),post)) :
 value=.val (.word 0) ∧EvmMemoryOperandAt post frame {words with stackSize:=words.stackSize+1} ∧
 post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,frame.toNat≤watched.toNat→watched≠frame+16→post.memory watched=s.memory watched) := by
 rw [source_stack_push_word] at run
 rw [evaluateHOLFiniteState_seq_line780] at run
 dsimp only at run
 cases callRun : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "stack_push") [stackPushWordValue]) with
 | mk result middle =>
   rw [callRun] at run
   dsimp only at run
   cases result with
   | none =>
     rw [evaluateHOLFiniteState_return] at run
     simp [evalHOLExact,shapeOfHOLExact] at run
     obtain ⟨valueEq,postEq⟩:=run
     subst post
     obtain ⟨physical,globals,locals,domain,endian,installed,pushFrame⟩:=stack_push_no_growth_discard_physical_context s middle frame words valid [stackPushWordValue] w 0 0 0 (push_word_args s w atW) inside fullDomain code callRun
     exact ⟨valueEq.symm,physical.after_context rfl rfl rfl,globals,domain,endian,installed,pushFrame⟩
   | some result =>
     have h : some result=some (PanSemResultExact.returned value) := congrArg Prod.fst (by dsimp only at run;exact run)
     have hr : result=PanSemResultExact.returned value := Option.some.inj h
     subst hr
     exact False.elim (discard_call_not_returned s (ofString "stack_push") [stackPushWordValue] value (by rw [callRun]))
#print axioms source_stack_push_word
#print axioms stack_push_word_returned_physical_context
end InitECandidate.Runtime
