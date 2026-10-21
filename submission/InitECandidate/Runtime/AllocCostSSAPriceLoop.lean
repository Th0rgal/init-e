import InitECandidate.Runtime.AllocCostSSANativePrice

/-!
# Whole-loop executed transfer for the price-parametric counter

`AllocCostSSALoopExecuted` proves the whole-loop transfer for the price-free
executed-work counter.  This module states and proves the same theorem for
`wordExecutionCost price`, so it applies to the native price
(`AllocCostSSANativePrice`) as well as to `loopWordPrice`.

The extra budget is the recursive `wecLoopExtra price`: it follows the *actual*
source iterations, charging `bodyBudget + backBudget` on every iteration whose
body is executed and whose result continues the loop.  Every executed back edge
is therefore charged at its own iteration; no whole-program maximum, no
per-iteration-uniform assumption and no cost oracle is used.

The one-step semantic premise `WecLoopStep` is a relation-level obligation: the
source and target cut states are related, the bodies run to the same result, the
successor states remain related (also after `decClock`), the clocks agree, and
this one target body run costs at most the source body run plus `bodyBudget`.
The only extra price premise is `hLoop`, the *local* price of the loop node
itself; it is discharged by `rfl`-level facts for the native price (`0` on both
sides) and by `1 ≤ 1` for `loopWordPrice`.
-/

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact
open InitECandidate.Runtime.WordToStack

/-- Dynamic extra cost of the actual source loop iterations for the
price-parametric counter. -/
noncomputable def wecLoopExtra {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (body : WordLangProgHOL (BitVec 64)) (names : WordLangNumSetHOL)
    (bodyBudget backBudget : Nat) (s : WordSemStateFiniteExact 64 C F) : Nat :=
  match _hs : cutState (names, .ln) s with
  | none => 0
  | some cutSource =>
      match _hr : fixClock cutSource (evaluate body cutSource) with
      | (result, middle) =>
          (bodyBudget + backBudget) +
            if wordSemContLoop result then
              (if _hc : middle.clock = 0 then 0
               else wecLoopExtra price body names bodyBudget backBudget
                 (decClock middle))
            else 0
termination_by s.clock
decreasing_by
  have hcut := cutState_clock_termdep _ _ _ _hs
  have hfix := fixClock_IMP_LESS_EQ _ _ _ _ _hr
  simp only [decClock]
  omega

/-- One-step simulation premise for the price-parametric whole-loop
transfer. -/
def WecLoopStep {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (names targetNames : WordLangNumSetHOL)
    (body targetBody : WordLangProgHOL (BitVec 64))
    (R : WordSemStateFiniteExact 64 C F → WordSemStateFiniteExact 64 C F → Prop)
    (bodyBudget : Nat) : Prop :=
  ∀ s t, R s t →
    (cutState (names, .ln) s = none ↔ cutState (targetNames, .ln) t = none) ∧
    ∀ cs ct, cutState (names, .ln) s = some cs →
      cutState (targetNames, .ln) t = some ct →
      R cs ct ∧
      (∀ result sm, fixClock cs (evaluate body cs) = (result, sm) →
        ∃ tm, fixClock ct (evaluate targetBody ct) = (result, tm) ∧
          R (decClock sm) (decClock tm) ∧
          tm.clock = sm.clock ∧
          wordExecutionCost price targetBody ct ≤ wordExecutionCost price body cs + bodyBudget)

/-- `wecLoopExtra` at a cut state that does not exist is zero. -/
theorem wecLoopExtra_none {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (body : WordLangProgHOL (BitVec 64)) (names : WordLangNumSetHOL)
    (bodyBudget backBudget : Nat) (s : WordSemStateFiniteExact 64 C F)
    (hs : cutState (names, .ln) s = none) :
    wecLoopExtra price body names bodyBudget backBudget s = 0 := by
  rw [wecLoopExtra]
  split
  · rfl
  · rename_i hsome
    rw [hs] at hsome
    cases hsome

/-- `wecLoopExtra` at an existing cut state, with the body run made explicit. -/
theorem wecLoopExtra_some_run {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (body : WordLangProgHOL (BitVec 64)) (names : WordLangNumSetHOL)
    (bodyBudget backBudget : Nat) (s cs : WordSemStateFiniteExact 64 C F)
    (result : Option (WordSemResult 64)) (middle : WordSemStateFiniteExact 64 C F)
    (hs : cutState (names, .ln) s = some cs)
    (hrun : fixClock cs (evaluate body cs) = (result, middle)) :
    wecLoopExtra price body names bodyBudget backBudget s =
      (bodyBudget + backBudget) +
        (if wordSemContLoop result then
          (if middle.clock = 0 then 0
           else wecLoopExtra price body names bodyBudget backBudget (decClock middle))
         else 0) := by
  rw [wecLoopExtra]
  split
  · rename_i hnone
    rw [hs] at hnone
    cases hnone
  · rename_i cutSource hsome
    rw [hs] at hsome
    injection hsome with h
    subst h
    cases hrun
    rfl

/-- **Whole-loop executed transfer, price-parametric.**  The target loop costs at
most the source loop plus the recursive per-iteration extra. -/
theorem wecLoop_executed_transfer {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (names targetNames exits targetExits : WordLangNumSetHOL)
    (body targetBody : WordLangProgHOL (BitVec 64))
    (bodyBudget backBudget : Nat)
    (R : WordSemStateFiniteExact 64 C F → WordSemStateFiniteExact 64 C F → Prop)
    (step : WecLoopStep price names targetNames body targetBody R bodyBudget)
    (hLoop : ∀ s t, R s t →
      price (.loop targetNames targetBody targetExits) t ≤
        price (.loop names body exits) s)
    (s t : WordSemStateFiniteExact 64 C F) (rel : R s t) :
    wordExecutionCost price (.loop targetNames targetBody targetExits) t ≤
      wordExecutionCost price (.loop names body exits) s +
        wecLoopExtra price body names bodyBudget backBudget s := by
  have main : ∀ n, ∀ (s t : WordSemStateFiniteExact 64 C F),
      s.clock = n → R s t →
      wordExecutionCost price (.loop targetNames targetBody targetExits) t ≤
        wordExecutionCost price (.loop names body exits) s +
          wecLoopExtra price body names bodyBudget backBudget s := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro s t hclock rel
      cases hs : cutState (names, .ln) s with
      | none =>
        have hnone : cutState (targetNames, .ln) t = none :=
          (step s t rel).1.mp hs
        rw [wec_loop_unfold_none price names body exits s hs,
          wec_loop_unfold_none price targetNames targetBody targetExits t hnone,
          wecLoopExtra_none price body names bodyBudget backBudget s hs]
        have hp := hLoop s t rel
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
            obtain ⟨tm, hrunT, hrelMid, hclockMid, hbodyWork⟩ :=
              hbodyRun result sm hrun
            rw [wec_loop_unfold_some price names body exits s cs hs,
              wec_loop_unfold_some price targetNames targetBody targetExits t ct ht,
              hrun, hrunT,
              wecLoopExtra_some_run price body names bodyBudget backBudget s cs result
                sm hs hrun]
            by_cases hcont : wordSemContLoop result
            · simp only [hcont, if_true]
              by_cases hzero : sm.clock = 0
              · have hzeroT : tm.clock = 0 := by omega
                rw [dif_pos hzero, dif_pos hzeroT, if_pos hzero]
                have hp := hLoop s t rel
                omega
              · have hzeroT : tm.clock ≠ 0 := by omega
                rw [dif_neg hzero, dif_neg hzeroT, if_neg hzero]
                have hdecLt : (decClock sm).clock < n := by
                  have hcut := cutState_clock_termdep (names, .ln) s cs hs
                  have hfix := fixClock_IMP_LESS_EQ cs result sm _ hrun
                  simp only [decClock] at *
                  omega
                have hrec := ih _ hdecLt (decClock sm) (decClock tm) rfl hrelMid
                simp only [wordSemSTOP]
                have hp := hLoop s t rel
                omega
            · simp only [hcont, if_false]
              simp
              have hp := hLoop s t rel
              omega
  exact main s.clock s t rfl rel

/-- The native price discharges the loop-node premise exactly: a structural
loop node costs `0` on both sides. -/
theorem wecLoopStep_native_hLoop {C F : Type}
    (names targetNames exits targetExits : WordLangNumSetHOL)
    (body targetBody : WordLangProgHOL (BitVec 64)) (bodyBudget backBudget : Nat)
    (R : WordSemStateFiniteExact 64 C F → WordSemStateFiniteExact 64 C F → Prop) :
    ∀ s t, R s t →
      nativeWordPrice (.loop targetNames targetBody targetExits) t ≤
        nativeWordPrice (.loop names body exits) s := by
  intro s t _
  simp only [nativeWordPrice]
  omega

/-- **Native whole-loop executed transfer**: the instance of the price-parametric
statement at `nativeWordPrice`, with no price premise left over. -/
theorem wecLoop_executed_transfer_native {C F : Type}
    (names targetNames exits targetExits : WordLangNumSetHOL)
    (body targetBody : WordLangProgHOL (BitVec 64))
    (bodyBudget backBudget : Nat)
    (R : WordSemStateFiniteExact 64 C F → WordSemStateFiniteExact 64 C F → Prop)
    (step : WecLoopStep nativeWordPrice names targetNames body targetBody R bodyBudget)
    (s t : WordSemStateFiniteExact 64 C F) (rel : R s t) :
    wordExecutionCost nativeWordPrice (.loop targetNames targetBody targetExits) t ≤
      wordExecutionCost nativeWordPrice (.loop names body exits) s +
        wecLoopExtra nativeWordPrice body names bodyBudget backBudget s :=
  wecLoop_executed_transfer nativeWordPrice names targetNames exits targetExits body targetBody
    bodyBudget backBudget R step
    (wecLoopStep_native_hLoop names targetNames exits targetExits body targetBody bodyBudget
      backBudget R) s t rel

#print axioms wecLoop_executed_transfer
#print axioms wecLoop_executed_transfer_native

end InitECandidate.Runtime.FineCost
