import InitECandidate.Runtime.AllocCostSSAExecuted
import Flapjack.Compiler.Backend.WordAlloc.Proofs.StateRelation
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocals
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.WordAlloc Flapjack.WordSemStateFiniteExact
open InitECandidate.Runtime.WordToStack

/-!
# Whole-loop executed SSA transfer

The static loop envelope in `AllocCostSSAControl` counts the body syntax once.
This module proves a *whole-loop* executed statement.  The extra budget is the
recursive `ssaLoopExtra`: it follows the actual source iterations, charging
`bodyBudget + backBudget` on every iteration whose body is executed and the
loop continues.  Thus every executed back-edge reconciliation is charged; no
whole-program AST maximum is used.

The semantic step is an explicit original hypothesis, not a cost oracle.  It
says that the source and target loop cut states are related, that the source
and target bodies run to the same result, that the post states remain related
(including after `decClock`), and that this one target body run costs at most
the source body run plus `bodyBudget`.  Instantiating it with the original
`ssaCcTransCorrectLoop` state relation is the remaining semantic plumbing; the
induction below is the whole-loop part and is complete.
-/

/-- Dynamic extra cost of the actual source loop iterations.  The recursive
call happens only when the body result continues the loop and the clock has
not run out, exactly as in `wordPathWork`. -/
noncomputable def ssaLoopExtra {width : Nat} [NeZero width] {C F : Type}
    (body : WordLangProgHOL (BitVec width)) (names : Spt Unit)
    (bodyBudget backBudget : Nat) (s : WordSemStateFiniteExact width C F) : Nat :=
  match _hs : cutState (names, .ln) s with
  | none => 0
  | some cutSource =>
      match _hr : fixClock cutSource (evaluate body cutSource) with
      | (result, middle) =>
          (bodyBudget + backBudget) +
            if wordSemContLoop result then
              (if _hc : middle.clock = 0 then 0
               else ssaLoopExtra body names bodyBudget backBudget
                 (Flapjack.WordSemStateFiniteExact.decClock middle))
            else 0
termination_by s.clock
decreasing_by
  have hcut := cutState_clock_termdep _ _ _ _hs
  have hfix := fixClock_IMP_LESS_EQ _ _ _ _ _hr
  simp only [Flapjack.WordSemStateFiniteExact.decClock]
  omega

/-- The recursive extra budget is finite and bounded by the actual source
loop work: each executed iteration contributes `bodyBudget + backBudget`, and
every executed body costs at least one work unit.  This is a dynamic bound,
not a whole-program maximum. -/
theorem ssaLoopExtra_le_work {width : Nat} [NeZero width] {C F : Type}
    (body : WordLangProgHOL (BitVec width)) (names exits : Spt Unit)
    (bodyBudget backBudget : Nat) (s : WordSemStateFiniteExact width C F) :
    ssaLoopExtra body names bodyBudget backBudget s ≤
      (bodyBudget + backBudget) * wordPathWork (.loop names body exits) s := by
  have main : ∀ n, ∀ (s : WordSemStateFiniteExact width C F), s.clock = n →
      ssaLoopExtra body names bodyBudget backBudget s ≤
        (bodyBudget + backBudget) * wordPathWork (.loop names body exits) s := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro s hclock
      rw [ssaLoopExtra, wordPathWork]
      cases hs : cutState (names, .ln) s with
      | none =>
        dsimp only
        omega
      | some cs =>
        dsimp only
        cases hrun : fixClock cs (evaluate body cs) with
        | mk result sm =>
          dsimp only
          by_cases hcont : wordSemContLoop result
          · rw [if_pos hcont, if_pos hcont]
            by_cases hzero : sm.clock = 0
            · simp only [hzero]
              have bodyOne := one_le_wordPathWork body cs
              have hpos : 0 < 1 + wordPathWork body cs := by omega
              have hbase := Nat.le_mul_of_pos_left (bodyBudget + backBudget) hpos
              rw [Nat.mul_comm] at hbase
              simpa using hbase
            · have bodyOne := one_le_wordPathWork body cs
              have hdecLt : (Flapjack.WordSemStateFiniteExact.decClock sm).clock < n := by
                have hcut := cutState_clock_termdep (names, .ln) s cs hs
                have hfix := fixClock_IMP_LESS_EQ cs result sm _ hrun
                simp only [Flapjack.WordSemStateFiniteExact.decClock] at *
                omega
              have hrec := ih _ hdecLt (Flapjack.WordSemStateFiniteExact.decClock sm) rfl
              simp only [hzero]
              simp only [wordSemSTOP]
              have hpos : 0 < 1 + wordPathWork body cs := by omega
              have hbase := Nat.le_mul_of_pos_left (bodyBudget + backBudget) hpos
              rw [Nat.mul_comm] at hbase
              have hsum := Nat.add_le_add hbase hrec
              rw [← Nat.mul_add] at hsum
              simpa [Nat.add_assoc] using hsum
          · rw [if_neg hcont, if_neg hcont]
            have bodyOne := one_le_wordPathWork body cs
            have hpos : 0 < 1 + wordPathWork body cs := by omega
            have hbase := Nat.le_mul_of_pos_left (bodyBudget + backBudget) hpos
            rw [Nat.mul_comm] at hbase
            simpa using hbase
  exact main s.clock s rfl

/-- One-step semantic simulation used by the whole-loop induction.  It is a
relation-level premise: same body result, related successor states, clock
agreement, and one-execution body work transfer. -/
def SsaLoopStep {width : Nat} [NeZero width] {C F : Type}
    (names targetNames : Spt Unit)
    (body targetBody : WordLangProgHOL (BitVec width))
    (R : WordSemStateFiniteExact width C F → WordSemStateFiniteExact width C F → Prop)
    (bodyBudget : Nat) : Prop :=
  ∀ s t, R s t →
    (cutState (names, .ln) s = none ↔ cutState (targetNames, .ln) t = none) ∧
    ∀ cs ct, cutState (names, .ln) s = some cs →
      cutState (targetNames, .ln) t = some ct →
      R cs ct ∧
      (∀ result sm, fixClock cs (evaluate body cs) = (result, sm) →
        ∃ tm, fixClock ct (evaluate targetBody ct) = (result, tm) ∧
          R (Flapjack.WordSemStateFiniteExact.decClock sm)
            (Flapjack.WordSemStateFiniteExact.decClock tm) ∧
          tm.clock = sm.clock ∧
          wordPathWork targetBody ct ≤ wordPathWork body cs + bodyBudget)

/-- The state relation used by the original SSA semantic loop proof:
`wordStateEqRel` plus the SSA-locals relation.  The whole-loop theorem is
relation-generic; this specialization records exactly which original relation
the one-step premise is meant to instantiate. -/
def SsaLoopStateRel {width : Nat} [NeZero width] {C F : Type}
    (ssa : Spt Nat) (next : Nat)
    (s t : WordSemStateFiniteExact width C F) : Prop :=
  Flapjack.WordAlloc.wordStateEqRel s t ∧
    ssaLocalsRel next ssa s.locals t.locals

/-- Whole-loop executed transfer.  The extra is charged recursively on the
actual source iterations; the strong induction is on the source clock, which
strictly decreases after `decClock` at every continuing iteration. -/
theorem ssaLoop_executed_transfer {width : Nat} [NeZero width] {C F : Type}
    (names targetNames exits targetExits : Spt Unit)
    (body targetBody : WordLangProgHOL (BitVec width))
    (bodyBudget backBudget : Nat)
    (R : WordSemStateFiniteExact width C F → WordSemStateFiniteExact width C F → Prop)
    (step : SsaLoopStep names targetNames body targetBody R bodyBudget)
    (s t : WordSemStateFiniteExact width C F) (rel : R s t) :
    wordPathWork (.loop targetNames targetBody targetExits) t ≤
      wordPathWork (.loop names body exits) s +
        ssaLoopExtra body names bodyBudget backBudget s := by
  have main : ∀ n, ∀ (s t : WordSemStateFiniteExact width C F),
      s.clock = n → R s t →
      wordPathWork (.loop targetNames targetBody targetExits) t ≤
        wordPathWork (.loop names body exits) s +
          ssaLoopExtra body names bodyBudget backBudget s := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro s t hclock rel
      rw [wordPathWork, wordPathWork]
      rw [ssaLoopExtra]
      cases hs : cutState (names, .ln) s with
      | none =>
        have hnone : cutState (targetNames, .ln) t = none :=
          (step s t rel).1.mp hs
        rw [hnone]
        dsimp only
        omega
      | some cs =>
        have htargetNotNone : cutState (targetNames, .ln) t ≠ none := by
          intro hnone
          have := (step s t rel).1.mpr hnone
          rw [hs] at this
          cases this
        cases ht : cutState (targetNames, .ln) t with
        | none => exact (htargetNotNone ht).elim
        | some ct =>
          obtain ⟨_hrelCut, hbody⟩ := step s t rel
          obtain ⟨_hrelCut2, hbodyRun⟩ := hbody cs ct hs ht
          cases hrun : fixClock cs (evaluate body cs) with
          | mk result sm =>
            simp only [hrun]
            obtain ⟨tm, hrunT, hrelMid, hclockMid, hbodyWork⟩ :=
              hbodyRun result sm hrun
            simp only [hrunT]
            by_cases hcont : wordSemContLoop result
            · rw [if_pos hcont, if_pos hcont, if_pos hcont]
              by_cases hzero : sm.clock = 0
              · have hzeroT : tm.clock = 0 := by omega
                simp only [hzero, hzeroT]
                simp
                omega
              · have hzeroT : tm.clock ≠ 0 := by omega
                simp only [hzero, hzeroT]
                have hdecLt : (Flapjack.WordSemStateFiniteExact.decClock sm).clock < n := by
                  have hcut := cutState_clock_termdep (names, .ln) s cs hs
                  have hfix := fixClock_IMP_LESS_EQ cs result sm _ hrun
                  simp only [Flapjack.WordSemStateFiniteExact.decClock] at *
                  omega
                have hrec := ih _ hdecLt (Flapjack.WordSemStateFiniteExact.decClock sm)
                  (Flapjack.WordSemStateFiniteExact.decClock tm) rfl hrelMid
                simp
                simp only [wordSemSTOP]
                omega
            · rw [if_neg hcont, if_neg hcont, if_neg hcont]
              simp
              omega
  exact main s.clock s t rfl rel

/-- The compiled loop starts with `loopSetup`.  Once its actual successful run
and executed setup charge are supplied, the whole `seq setup loop` is covered,
not just the inner `wordPathWork` recurrence. -/
theorem ssaLoop_compiled_executed_transfer {width : Nat} [NeZero width] {C F : Type}
    (names targetNames exits targetExits : Spt Unit)
    (body targetBody : WordLangProgHOL (BitVec width))
    (setup : WordLangProgHOL (BitVec width)) (setupBudget : Nat)
    (bodyBudget backBudget : Nat)
    (R : WordSemStateFiniteExact width C F → WordSemStateFiniteExact width C F → Prop)
    (step : SsaLoopStep names targetNames body targetBody R bodyBudget)
    (s : WordSemStateFiniteExact width C F)
    (start middle : WordSemStateFiniteExact width C F)
    (setupRun : evaluate setup start = (none, middle))
    (setupWork : wordPathWork setup start ≤ setupBudget)
    (rel : R s middle) :
    wordPathWork (.seq setup (.loop targetNames targetBody targetExits)) start ≤
      wordPathWork (.loop names body exits) s +
        (1 + setupBudget + ssaLoopExtra body names bodyBudget backBudget s) := by
  rw [wordPathWork_seq, setupRun]
  dsimp only
  have inner := ssaLoop_executed_transfer names targetNames exits targetExits
    body targetBody bodyBudget backBudget R step s middle rel
  omega

/-- Whole-loop transfer stated over the original `wordStateEqRel` +
`ssaLocalsRel` relation.  The one-step premise remains explicit. -/
theorem ssaLoop_executed_transfer_originalRel {width : Nat} [NeZero width] {C F : Type}
    (names targetNames exits targetExits : Spt Unit)
    (body targetBody : WordLangProgHOL (BitVec width))
    (bodyBudget backBudget : Nat) (ssa : Spt Nat) (next : Nat)
    (step : SsaLoopStep names targetNames body targetBody
      (SsaLoopStateRel (width := width) (C := C) (F := F) ssa next) bodyBudget)
    (s t : WordSemStateFiniteExact width C F)
    (rel : SsaLoopStateRel (width := width) (C := C) (F := F) ssa next s t) :
    wordPathWork (.loop targetNames targetBody targetExits) t ≤
      wordPathWork (.loop names body exits) s +
        ssaLoopExtra body names bodyBudget backBudget s :=
  ssaLoop_executed_transfer names targetNames exits targetExits body targetBody
    bodyBudget backBudget _ step s t rel

#print axioms ssaLoopExtra
#print axioms ssaLoopExtra_le_work
#print axioms ssaLoop_executed_transfer
#print axioms ssaLoop_compiled_executed_transfer
#print axioms ssaLoop_executed_transfer_originalRel
end InitECandidate.Runtime.FineCost
