import InitECandidate.Runtime.StackPushNoGrowthCallPhysicalContext
import InitECandidate.Runtime.PcAddReturnPhysicalContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
/-- The real boolean push helper: a genuine zero test and one of two real
four-limb constant struct pushes. -/
def stackPushBoolBody : ProgHOL 64:=sourceFunctionBody Guest.guestFn_stack_push_bool

def stackPushBoolOne : ExpHOL 64:=.rstruct [.const 1,.const 0,.const 0,.const 0]

def stackPushBoolZero : ExpHOL 64:=.rstruct [.const 0,.const 0,.const 0,.const 0]

theorem source_stack_push_bool :
 stackPushBoolBody=.seq (.ite (.cmp Cmp.notEqual (.var .local (ofString "b")) (.const 0)) (.call (some (none,none)) (ofString "stack_push") [stackPushBoolOne]) (.call (some (none,none)) (ofString "stack_push") [stackPushBoolZero])) (.return (.const 0)) := by
 simp only [stackPushBoolBody,stackPushBoolOne,stackPushBoolZero,sourceFunctionBody_eq_structural];rfl
private theorem push_bool_args_one {F : Type} (s : PanSemStateFiniteExact 64 F) :
 evalListHOLFinite s (h:=fun x=>Classical.propDecidable (s.memaddrs x)) [stackPushBoolOne]=some [fundingU256 1 0 0 0] := by
 simp [stackPushBoolOne,fundingU256,evalListHOLFinite,evalListHOLExact,evalHOLExact]
private theorem push_bool_args_zero {F : Type} (s : PanSemStateFiniteExact 64 F) :
 evalListHOLFinite s (h:=fun x=>Classical.propDecidable (s.memaddrs x)) [stackPushBoolZero]=some [fundingU256 0 0 0 0] := by
 simp [stackPushBoolZero,fundingU256,evalListHOLFinite,evalListHOLExact,evalHOLExact]
/-- The real boolean push helper closes a concrete operand state: the checked
boolean word selects one of two constant four-limb pushes and the helper
returns zero without touching PC. -/
theorem stack_push_bool_returned_physical_context {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (frame : BitVec 64)
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s frame words)
 (b : BitVec 64) (value : ValueHOL 64)
 (atB : s.locals.lookup (ofString "b")=some (.val (.word b)))
 (inside : words.stackSize.toNat<words.stackCapacity.toNat)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s stackPushBoolBody=(some (.returned value),post)) :
 value=.val (.word 0) ∧EvmMemoryOperandAt post frame {words with stackSize:=words.stackSize+1} ∧
 post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,frame.toNat≤watched.toNat→watched≠frame+16→post.memory watched=s.memory watched) := by
 rw [source_stack_push_bool] at run
 have branch : evaluateHOLFiniteState s (.ite (.cmp Cmp.notEqual (.var .local (ofString "b")) (.const 0)) (.call (some (none,none)) (ofString "stack_push") [stackPushBoolOne]) (.call (some (none,none)) (ofString "stack_push") [stackPushBoolZero]))=
   if b=0 then evaluateHOLFiniteState s (.call (some (none,none)) (ofString "stack_push") [stackPushBoolZero]) else evaluateHOLFiniteState s (.call (some (none,none)) (ofString "stack_push") [stackPushBoolOne]) := by
  rw [evaluateHOLFiniteState_ite]
  simp [evalHOLExact,atB,Compiler.Encoders.Asm.wordCmpHOL]
 rw [evaluateHOLFiniteState_seq_line780,branch] at run
 by_cases zero : b=0
 · rw [if_pos zero] at run
   cases callRun : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "stack_push") [stackPushBoolZero]) with
   | mk result middle =>
     rw [callRun] at run
     dsimp only at run
     cases result with
     | none =>
       rw [evaluateHOLFiniteState_return] at run
       simp [evalHOLExact,shapeOfHOLExact,Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL] at run
       obtain ⟨valueEq,postEq⟩:=run
       subst post
       obtain ⟨physical,globals,locals,domain,endian,installed,pushFrame⟩:=stack_push_no_growth_discard_physical_context s middle frame words valid [stackPushBoolZero] 0 0 0 0 (push_bool_args_zero s) inside fullDomain code callRun
       exact ⟨valueEq.symm,physical.after_context rfl rfl rfl,globals,domain,endian,installed,pushFrame⟩
     | some result =>
       have h : some result=some (PanSemResultExact.returned value) := congrArg Prod.fst (by dsimp only at run;exact run)
       have hr : result=PanSemResultExact.returned value := Option.some.inj h
       subst hr
       exact False.elim (discard_call_not_returned s (ofString "stack_push") [stackPushBoolZero] value (by rw [callRun]))
 · rw [if_neg zero] at run
   cases callRun : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "stack_push") [stackPushBoolOne]) with
   | mk result middle =>
     rw [callRun] at run
     dsimp only at run
     cases result with
     | none =>
       rw [evaluateHOLFiniteState_return] at run
       simp [evalHOLExact,shapeOfHOLExact,Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL] at run
       obtain ⟨valueEq,postEq⟩:=run
       subst post
       obtain ⟨physical,globals,locals,domain,endian,installed,pushFrame⟩:=stack_push_no_growth_discard_physical_context s middle frame words valid [stackPushBoolOne] 1 0 0 0 (push_bool_args_one s) inside fullDomain code callRun
       exact ⟨valueEq.symm,physical.after_context rfl rfl rfl,globals,domain,endian,installed,pushFrame⟩
     | some result =>
       have h : some result=some (PanSemResultExact.returned value) := congrArg Prod.fst (by dsimp only at run;exact run)
       have hr : result=PanSemResultExact.returned value := Option.some.inj h
       subst hr
       exact False.elim (discard_call_not_returned s (ofString "stack_push") [stackPushBoolOne] value (by rw [callRun]))
#print axioms source_stack_push_bool
#print axioms stack_push_bool_returned_physical_context
end InitECandidate.Runtime
