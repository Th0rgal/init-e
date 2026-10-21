import InitECandidate.Runtime.AllocCostSSAPriceLoop
import Flapjack.Compiler.Backend.WordAlloc.Proofs.StateRelation
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocals

/-!
# Allocation-stage executed-cost transfer at the native price

The entry points proved so far are stated over a value-equal stack (`sValEq`),
which is what the call and return-handler transports consume.  This module
wires them into the *original* allocator relation used by the SSA/allocation
correctness proof:

`SsaAllocRel ssa next s t  :=  wordStateEqRel s t ∧ ssaLocalsRel next ssa s.locals t.locals`

`wordStateEqRel` fixes `stack`, `code`, `clock`, `termdep` and every other
machine field, and leaves only the *locals* (and the permutation oracle) free;
`ssaLocalsRel` is the original statement that the allocated locals are the SSA
renaming of the source ones.  Hence

* `stage_sValEq`: the two stacks are value-equal, which is exactly the entry
  point of `wordExecutionCost_nativeWordPrice_stack_variant` and of the callee
  body / return-continuation transfers;
* `wecLoop_executed_transfer_stage`: the whole-loop transfer over that original
  relation, with the per-body one-step premise and **no target-run budget**;
* `wecLoop_executed_transfer_stage_swap`: the same when the target loop is run
  from the stack-transported state, i.e. the state the allocator's own
  renamings actually produce.

The source-reached branches are preserved: the statements are about the actual
`evaluate` runs of the source loop and the recursive per-iteration charge, not
about a supplied target cost.
-/

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.WordAlloc
open Flapjack.Compiler.Backend.WordAlloc
open InitECandidate.Runtime.WordToStack

/-- The original allocator relation: every machine field agrees, and the
allocated locals are related to the source locals by the SSA renaming. -/
def SsaAllocRel {C F : Type} (ssa : Spt Nat) (next : Nat)
    (s t : WordSemStateFiniteExact 64 C F) : Prop :=
  wordStateEqRel s t ∧ ssaLocalsRel next ssa s.locals t.locals

theorem stage_stack {C F : Type} {ssa : Spt Nat} {next : Nat}
    {s t : WordSemStateFiniteExact 64 C F} (h : SsaAllocRel ssa next s t) :
    t.stack = s.stack := by
  have h' := h.1
  simp only [wordStateEqRel] at h'
  tauto

theorem stage_code {C F : Type} {ssa : Spt Nat} {next : Nat}
    {s t : WordSemStateFiniteExact 64 C F} (h : SsaAllocRel ssa next s t) :
    t.code = s.code := by
  have h' := h.1
  simp only [wordStateEqRel] at h'
  tauto

theorem stage_clock {C F : Type} {ssa : Spt Nat} {next : Nat}
    {s t : WordSemStateFiniteExact 64 C F} (h : SsaAllocRel ssa next s t) :
    t.clock = s.clock := by
  have h' := h.1
  simp only [wordStateEqRel] at h'
  tauto

theorem stage_termdep {C F : Type} {ssa : Spt Nat} {next : Nat}
    {s t : WordSemStateFiniteExact 64 C F} (h : SsaAllocRel ssa next s t) :
    t.termdep = s.termdep := by
  have h' := h.1
  simp only [wordStateEqRel] at h'
  tauto

theorem stage_stackSize {C F : Type} {ssa : Spt Nat} {next : Nat}
    {s t : WordSemStateFiniteExact 64 C F} (h : SsaAllocRel ssa next s t) :
    t.stackSize = s.stackSize := by
  have h' := h.1
  simp only [wordStateEqRel] at h'
  tauto

theorem stage_stackLimit {C F : Type} {ssa : Spt Nat} {next : Nat}
    {s t : WordSemStateFiniteExact 64 C F} (h : SsaAllocRel ssa next s t) :
    t.stackLimit = s.stackLimit := by
  have h' := h.1
  simp only [wordStateEqRel] at h'
  tauto

theorem stage_stackMax {C F : Type} {ssa : Spt Nat} {next : Nat}
    {s t : WordSemStateFiniteExact 64 C F} (h : SsaAllocRel ssa next s t) :
    t.stackMax = s.stackMax := by
  have h' := h.1
  simp only [wordStateEqRel] at h'
  tauto

theorem stage_handler {C F : Type} {ssa : Spt Nat} {next : Nat}
    {s t : WordSemStateFiniteExact 64 C F} (h : SsaAllocRel ssa next s t) :
    t.handler = s.handler := by
  have h' := h.1
  simp only [wordStateEqRel] at h'
  tauto

theorem stage_gcFun {C F : Type} {ssa : Spt Nat} {next : Nat}
    {s t : WordSemStateFiniteExact 64 C F} (h : SsaAllocRel ssa next s t) :
    t.gcFun = s.gcFun := by
  have h' := h.1
  simp only [wordStateEqRel] at h'
  tauto

theorem stage_memory {C F : Type} {ssa : Spt Nat} {next : Nat}
    {s t : WordSemStateFiniteExact 64 C F} (h : SsaAllocRel ssa next s t) :
    t.memory = s.memory := by
  have h' := h.1
  simp only [wordStateEqRel] at h'
  tauto

theorem stage_fpRegs {C F : Type} {ssa : Spt Nat} {next : Nat}
    {s t : WordSemStateFiniteExact 64 C F} (h : SsaAllocRel ssa next s t) :
    t.fpRegs = s.fpRegs := by
  have h' := h.1
  simp only [wordStateEqRel] at h'
  tauto

theorem stage_store {C F : Type} {ssa : Spt Nat} {next : Nat}
    {s t : WordSemStateFiniteExact 64 C F} (h : SsaAllocRel ssa next s t) :
    t.store = s.store := by
  have h' := h.1
  simp only [wordStateEqRel] at h'
  tauto

theorem stage_localsSize {C F : Type} {ssa : Spt Nat} {next : Nat}
    {s t : WordSemStateFiniteExact 64 C F} (h : SsaAllocRel ssa next s t) :
    t.localsSize = s.localsSize := by
  have h' := h.1
  simp only [wordStateEqRel] at h'
  tauto


/-- Value equality of a stack with itself. -/
theorem sValEq_refl_stack (xs : List (WordSemStackFrame 64)) :
    WordSemStackEq.sValEq xs xs := by
  induction xs with
  | nil => simp [WordSemStackEq.sValEq]
  | cons x rest ih =>
      simp only [WordSemStackEq.sValEq]
      refine ⟨ih, ?_⟩
      cases x with
      | stackFrame n ls0 ls opt =>
          cases opt with
          | none => simp [WordSemStackEq.sFrameValEq]
          | some y => simp [WordSemStackEq.sFrameValEq]

/-- The original allocator relation gives value-equal stacks, which is the entry
point of the native stack transport. -/
theorem stage_sValEq {C F : Type} {ssa : Spt Nat} {next : Nat}
    {s t : WordSemStateFiniteExact 64 C F} (h : SsaAllocRel ssa next s t) :
    WordSemStackEq.sValEq s.stack t.stack := by
  rw [stage_stack h]
  exact sValEq_refl_stack s.stack

/-- **Whole-loop allocation-stage transfer at the native price.**  From the
original allocator relation, the allocated loop's executed native cost is at
most the source loop's plus the recursive per-iteration extra.  The one-step
premise is the usual body simulation; there is no target-run budget. -/
theorem wecLoop_executed_transfer_stage {C F : Type}
    (ssa : Spt Nat) (next : Nat)
    (names targetNames exits targetExits : WordLangNumSetHOL)
    (body targetBody : WordLangProgHOL (BitVec 64))
    (bodyBudget backBudget : Nat)
    (step : @WecLoopStep C F nativeWordPrice names targetNames body targetBody
      (SsaAllocRel ssa next) bodyBudget)
    (s t : WordSemStateFiniteExact 64 C F) (rel : SsaAllocRel ssa next s t) :
    wordExecutionCost nativeWordPrice (.loop targetNames targetBody targetExits) t ≤
      wordExecutionCost nativeWordPrice (.loop names body exits) s +
        wecLoopExtra nativeWordPrice body names bodyBudget backBudget s :=
  wecLoop_executed_transfer_native names targetNames exits targetExits body targetBody
    bodyBudget backBudget (SsaAllocRel ssa next) step s t rel

/-- The same transfer when the target loop runs from the stack-transported state
the allocator's renamings actually produce. -/
theorem wecLoop_executed_transfer_stage_swap {C F : Type}
    (ssa : Spt Nat) (next : Nat)
    (names targetNames exits targetExits : WordLangNumSetHOL)
    (body targetBody : WordLangProgHOL (BitVec 64))
    (bodyBudget backBudget : Nat)
    (step : @WecLoopStep C F nativeWordPrice names targetNames body targetBody
      (SsaAllocRel ssa next) bodyBudget)
    (s t : WordSemStateFiniteExact 64 C F) (rel : SsaAllocRel ssa next s t)
    (ys : List (WordSemStackFrame 64))
    (hval : WordSemStackEq.sValEq t.stack ys)
    (hne : (evaluate (.loop targetNames targetBody targetExits) t).1 ≠
      some WordSemResult.error) :
    wordExecutionCost nativeWordPrice (.loop targetNames targetBody targetExits)
        { t with stack := ys } ≤
      wordExecutionCost nativeWordPrice (.loop names body exits) s +
        wecLoopExtra nativeWordPrice body names bodyBudget backBudget s := by
  rw [wordExecutionCost_nativeWordPrice_stack_variant
    (.loop targetNames targetBody targetExits) t ys hval hne]
  exact wecLoop_executed_transfer_stage ssa next names targetNames exits targetExits
    body targetBody bodyBudget backBudget step s t rel

#print axioms stage_stack
#print axioms stage_sValEq
#print axioms wecLoop_executed_transfer_stage
#print axioms wecLoop_executed_transfer_stage_swap

end InitECandidate.Runtime.FineCost
