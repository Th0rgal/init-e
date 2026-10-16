import InitECandidate.Runtime.StackAllocCallBudget
import InitECandidate.Runtime.StackAllocStoreBudget
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CompCorrect

namespace InitECandidate.Runtime.StackAlloc.Zero
open Flapjack Flapjack.Compiler.Backend Flapjack.StackSemStateOps
open Flapjack.Compiler.Backend.StackLang Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend.StackProps Flapjack.StackSemMeasure
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect

/-- Allocation lowering needs no extra clock for certified code and oracle.
The original simulation premises and all original postconditions are retained.
All recursive execution sites are discharged by the evaluator's measure. -/
theorem goal_all {width : Nat} [NeZero width] {C F : Type} (anything : WordSemGcFun width)
    (cr : CompileFn width C) :
    ∀ (mm : Nat × Nat) (p : HolProg width) (s : StackSemStateFiniteExact width C F),
      stackSemMeasure p s = mm → allocationFree p = true → FreeState s → ZeroGoal anything cr p s := by
  intro mm
  induction mm using EvaluateAddClock.lexNat_wf.induction with
  | _ mm ih =>
  intro p s hm free stateFree
  subst hm
  have ihp : IH anything cr p s := fun q u hlt freeQ freeU => ih _ hlt q u rfl freeQ freeU
  cases p with
  | skip => exact goal_skip anything cr s
  | halt v => exact goal_halt anything cr s v
  | tick => exact goal_tick anything cr s
  | ret v => exact goal_ret anything cr s v
  | raise v => exact goal_raise anything cr s v
  | «break» v => exact goal_break anything cr s v
  | «continue» v => exact goal_continue anything cr s v
  | inst i => exact goal_inst anything cr s i
  | get v name => exact goal_get anything cr s v name
  | set name v => exact goal_set anything cr s name v
  | opCurrHeap b v src => exact goal_opCurrHeap anything cr s b v src
  | alloc k => simp [allocationFree] at free
  | storeConsts t1 t2 stub =>
      cases stub with
      | none => exact goal_storeConsts anything cr s t1 t2
      | some loc => simp [allocationFree] at free
  | seq c1 c2 => exact goal_seq anything cr s c1 c2 free stateFree ihp
  | ite cmp r1 ri c1 c2 => exact goal_ite anything cr s cmp r1 ri c1 c2 free stateFree ihp
  | loop c1 => exact goal_loop anything cr s c1 free stateFree ihp
  | jumpLower r1 r2 dest => exact goal_jumpLower anything cr s r1 r2 dest free stateFree ihp
  | rawCall dest => exact goal_rawCall anything cr s dest free stateFree ihp
  | call ret dest handler =>
      rcases ret with _ | ⟨retH, link, l1, l2⟩
      · exact goal_call_none anything cr s dest handler free stateFree ihp
      · exact goal_call_some anything cr s retH link l1 l2 dest handler free stateFree ihp
  | install a b c d e => simp [allocationFree] at free
  | shMemOp op v addr => exact goal_shMemOp anything cr s op v addr
  | codeBufferWrite a b => exact goal_codeBufferWrite anything cr s a b
  | dataBufferWrite a b => exact goal_dataBufferWrite anything cr s a b
  | ffi fi p1 p2 p3 p4 p5 => exact goal_ffi anything cr s fi p1 p2 p3 p4 p5
  | locValue v l1 l2 => exact goal_locValue anything cr s v l1 l2
  | stackAlloc k => exact goal_stackAlloc anything cr s k
  | stackFree k => exact goal_stackFree anything cr s k
  | stackLoad a k => exact goal_stackLoad anything cr s a k
  | stackLoadAny a rn => exact goal_stackLoadAny anything cr s a rn
  | stackStore a k => exact goal_stackStore anything cr s a k
  | stackStoreAny a rn => exact goal_stackStoreAny anything cr s a rn
  | stackGetSize a => exact goal_stackGetSize anything cr s a
  | stackSetSize a => exact goal_stackSetSize anything cr s a
  | bitmapLoad a v => exact goal_bitmapLoad anything cr s a v

/-- Whole-stage zero-clock simulation, with no recursive simulation assumptions. -/
theorem allocationFree_same_clock {width : Nat} [NeZero width] {C F : Type}
    (anything : WordSemGcFun width) (cr : CompileFn width C)
    (p : HolProg width) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width)) (c : DataToWord.Config)
    (regs : HolFiniteMapExact Nat (WordLocW width))
    (free : allocationFree p = true) (stateFree : FreeState s)
    (run : evaluate (p, s) = (r, t)) (notError : r ≠ some .error)
    (arg : StackProps.allocArg p) (pre : Pre cr c s regs) :
    ∃ regs1, evaluate (p, Res anything cr c s regs) =
      (r, Res anything cr c t regs1) ∧ Post r t regs1 := by
  obtain ⟨ck, rfl, regs1, targetRun, post⟩ :=
    goal_all anything cr _ p s rfl free stateFree r t 0 0 c regs run notError arg pre
  refine ⟨regs1, ?_, post⟩
  simpa only [allocationFree_comp 0 0 p free, tgt_zero] using targetRun

#print axioms allocationFree_same_clock
end InitECandidate.Runtime.StackAlloc.Zero
