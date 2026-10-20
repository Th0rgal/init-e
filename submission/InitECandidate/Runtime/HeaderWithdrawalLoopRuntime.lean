import InitECandidate.Runtime.CountedLoop
import InitECandidate.Runtime.HeaderWithdrawalLoopFrame
import InitECandidate.Runtime.EncodeWithdrawalCallBound
import InitECandidate.Runtime.SourceCostAdapter
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- A straight-line program costs no tick from any state, with no code premise. -/
theorem runBounded_zero_of_extStraightLine {F : Type} (state : PanSemStateFiniteExact 64 F)
    (program : ProgHOL 64) (supported : extStraightLine program = true) : RunBounded state program 0 := by
  have clock := clockPreserving_of_extStraightLine (F := F) program supported state
  refine ⟨by rw [clock]; omega, by rw [clock], ?_⟩
  exact evaluate_extStraightLine_no_timeout program supported state

/-- The two stores of one iteration are straight-line: their run costs no tick. -/
theorem wdSliceLoopStores_extStraightLine : extStraightLine wdSliceLoopStores = true := by
  decide_cbv


/-- **Counted loop clock bound with state-dependent per-iteration bounds.** This is the `RunBounded`
analogue of `countedWhile_run`: the per-iteration cost is not required to be a uniform `ProgBounded`,
only a `RunBounded` under a preserved state predicate `P`. -/
theorem countedWhile_runBounded (counter : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower)
    (K step : BitVec 64) (small : K.toNat + step.toNat < 2 ^ 63) (positive : 0 < step.toNat)
    {body : ProgHOL 64} {cost : Nat}
    (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (run : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (w : BitVec 64), P state →
      state.code = originalRuntimeCode →
      state.locals.lookup counter = some (.val (.word w)) → cost ≤ state.clock →
      RunBounded state body cost)
    (keep : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (w : BitVec 64), P state →
      state.code = originalRuntimeCode →
      state.locals.lookup counter = some (.val (.word w)) →
      (evaluateHOLFiniteState state body).1 = none → P (evaluateHOLFiniteState state body).2)
    (advance : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (w : BitVec 64), P state →
      state.locals.lookup counter = some (.val (.word w)) →
      (evaluateHOLFiniteState state body).1 = none →
      (evaluateHOLFiniteState state body).2.locals.lookup counter = some (.val (.word (w + step))) ∧
      (evaluateHOLFiniteState state body).2.code = state.code)
    (noContinue : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (w : BitVec 64), P state →
      (evaluateHOLFiniteState state body).1 ≠ some .continue)
    (decrease : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), P state → P (decClockHOLFinite state)) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), P state →
      state.code = originalRuntimeCode →
      ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) → w.toNat ≤ K.toNat + step.toNat →
      K.toNat - w.toNat = n → n * (cost + 1) ≤ state.clock →
      state.clock ≤ (evaluateHOLFiniteState state
        (.while (.cmp op (.var .local counter) (.const K)) body)).2.clock + n * (cost + 1) ∧
        (evaluateHOLFiniteState state
          (.while (.cmp op (.var .local counter) (.const K)) body)).2.clock ≤ state.clock ∧
        (evaluateHOLFiniteState state
          (.while (.cmp op (.var .local counter) (.const K)) body)).1 ≠ some .timeOut := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F state pstate code w atCounter within distance budget
    have condition := eval_counted_condition state counter op hop K w (by omega) (by omega) atCounter
    rw [evaluateHOLFiniteState_while_total, condition]
    by_cases lt : w.toNat < K.toNat
    · rw [if_pos lt]
      simp only [show (1 : BitVec 64) ≠ 0 by decide, if_true, ne_eq, not_false_eq_true]
      have positiveRank : 0 < n := by omega
      have clock : state.clock ≠ 0 := by
        have : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
        omega
      rw [if_neg clock]
      rw [fixClockHOLFinite_evaluateState]
      have pclock : P (decClockHOLFinite state) := decrease state pstate
      have codeClock : (decClockHOLFinite state).code = originalRuntimeCode := by
        simpa [decClockHOLFinite] using code
      have atClock : (decClockHOLFinite state).locals.lookup counter = some (.val (.word w)) := by
        simpa [decClockHOLFinite] using atCounter
      have stepRun := run (decClockHOLFinite state) w pclock codeClock atClock (by
        change cost ≤ state.clock - 1
        have : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
        omega)
      unfold RunBounded at stepRun
      have meta' := evaluateHOLFiniteState_metadata (decClockHOLFinite state) body
      cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
      | mk result middle =>
        rw [bodyRun] at stepRun meta'
        obtain ⟨spent, kept, safe⟩ := stepRun
        change state.clock - 1 ≤ middle.clock + cost at spent
        change middle.clock ≤ state.clock - 1 at kept
        have oneIteration : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
        cases result with
        | none =>
          dsimp only
          have adv := advance (decClockHOLFinite state) w pclock atClock (by rw [bodyRun])
          obtain ⟨nextCounter, nextCode⟩ := adv
          have nextCounter' : middle.locals.lookup counter = some (.val (.word (w + step))) := by
            simpa [bodyRun] using nextCounter
          have nextCode' : middle.code = (decClockHOLFinite state).code := by
            simpa [bodyRun] using nextCode
          have keepP : P middle := by
            simpa [bodyRun] using keep (decClockHOLFinite state) w pclock codeClock atClock
              (by rw [bodyRun])
          have natural : (w + step).toNat = w.toNat + step.toNat := BitVec.toNat_add_of_lt (by omega)
          have nextRank : K.toNat - (w + step).toNat < n := by rw [natural]; omega
          have tail := ih (K.toNat - (w + step).toNat) nextRank middle keepP (nextCode'.trans codeClock) (w + step)
            nextCounter' (by rw [natural]; omega) rfl (by
              have : (K.toNat - (w + step).toNat) * (cost + 1) + (cost + 1) ≤ n * (cost + 1) := by
                rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
              omega)
          obtain ⟨t1, t2, t3⟩ := tail
          refine ⟨?_, by omega, t3⟩
          have : (K.toNat - (w + step).toNat) * (cost + 1) + (cost + 1) ≤ n * (cost + 1) := by
            rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
          omega
        | some r =>
          cases r with
          | «continue» =>
            have hc : (evaluateHOLFiniteState (decClockHOLFinite state) body).1 = some .continue := by
              rw [bodyRun]
            exact absurd hc (noContinue (decClockHOLFinite state) w pclock)
          | «break» => exact ⟨by simp; omega, by simp; omega, by simp⟩
          | timeOut => exact absurd rfl safe
          | _ => exact ⟨by simp; omega, by simp; omega, by simp⟩
    · rw [if_neg lt]
      simp


/-- The loop condition of statement 46 reads its bound from the `nwd` local instead of a constant:
the same value gives the same comparison result. -/
theorem eval_var_condition {F : Type} (state : PanSemStateFiniteExact 64 F) (counter bound : MlS)
    (op : Cmp) (hop : op = .less ∨ op = .lower) (K w : BitVec 64)
    (hK : K.toNat < 2 ^ 63) (hw : w.toNat < 2 ^ 63)
    (atCounter : state.locals.lookup counter = some (.val (.word w)))
    (atBound : state.locals.lookup bound = some (.val (.word K))) :
    evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      (.cmp op (.var .local counter) (.var .local bound)) =
      some (.val (.word (if w.toNat < K.toNat then 1 else 0))) := by
  rw [evalHOLFinite_eq_toExact]
  rcases hop with rfl | rfl
  · simp only [evalHOLExact, atCounter, atBound]
    simp only [Compiler.Encoders.Asm.wordCmpHOL, holAsmSignedLess_small w K hw hK]
    by_cases lt : w.toNat < K.toNat <;> simp [lt]
  · simp only [evalHOLExact, atCounter, atBound]
    simp only [Compiler.Encoders.Asm.wordCmpHOL]
    by_cases lt : w.toNat < K.toNat <;> simp [lt, BitVec.lt_def]

#print axioms eval_var_condition

theorem countedWhile_runBounded_var (counter bound : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower)
    (K step : BitVec 64) (small : K.toNat + step.toNat < 2 ^ 63) (positive : 0 < step.toNat)
    {body : ProgHOL 64} {cost : Nat}
    (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (run : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (w : BitVec 64), P state →
      state.code = originalRuntimeCode →
      state.locals.lookup counter = some (.val (.word w)) → cost ≤ state.clock →
      RunBounded state body cost)
    (keep : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (w : BitVec 64), P state →
      state.code = originalRuntimeCode →
      state.locals.lookup counter = some (.val (.word w)) →
      (evaluateHOLFiniteState state body).1 = none → P (evaluateHOLFiniteState state body).2)
    (advance : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (w : BitVec 64), P state →
      state.locals.lookup counter = some (.val (.word w)) →
      (evaluateHOLFiniteState state body).1 = none →
      (evaluateHOLFiniteState state body).2.locals.lookup counter = some (.val (.word (w + step))) ∧
      (evaluateHOLFiniteState state body).2.code = state.code)
    (noContinue : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (w : BitVec 64), P state →
      (evaluateHOLFiniteState state body).1 ≠ some .continue)
    (decrease : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), P state → P (decClockHOLFinite state))
    (atBound : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), P state →
      state.locals.lookup bound = some (.val (.word K))) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), P state →
      state.code = originalRuntimeCode →
      ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) → w.toNat ≤ K.toNat + step.toNat →
      K.toNat - w.toNat = n → n * (cost + 1) ≤ state.clock →
      state.clock ≤ (evaluateHOLFiniteState state
        (.while (.cmp op (.var .local counter) (.var .local bound)) body)).2.clock + n * (cost + 1) ∧
        (evaluateHOLFiniteState state
          (.while (.cmp op (.var .local counter) (.var .local bound)) body)).2.clock ≤ state.clock ∧
        (evaluateHOLFiniteState state
          (.while (.cmp op (.var .local counter) (.var .local bound)) body)).1 ≠ some .timeOut := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F state pstate code w atCounter within distance budget
    have condition := eval_var_condition state counter bound op hop K w (by omega) (by omega) atCounter
      (atBound state pstate)
    rw [evaluateHOLFiniteState_while_total, condition]
    by_cases lt : w.toNat < K.toNat
    · rw [if_pos lt]
      simp only [show (1 : BitVec 64) ≠ 0 by decide, if_true, ne_eq, not_false_eq_true]
      have positiveRank : 0 < n := by omega
      have clock : state.clock ≠ 0 := by
        have : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
        omega
      rw [if_neg clock]
      rw [fixClockHOLFinite_evaluateState]
      have pclock : P (decClockHOLFinite state) := decrease state pstate
      have codeClock : (decClockHOLFinite state).code = originalRuntimeCode := by
        simpa [decClockHOLFinite] using code
      have atClock : (decClockHOLFinite state).locals.lookup counter = some (.val (.word w)) := by
        simpa [decClockHOLFinite] using atCounter
      have stepRun := run (decClockHOLFinite state) w pclock codeClock atClock (by
        change cost ≤ state.clock - 1
        have : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
        omega)
      unfold RunBounded at stepRun
      have meta' := evaluateHOLFiniteState_metadata (decClockHOLFinite state) body
      cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
      | mk result middle =>
        rw [bodyRun] at stepRun meta'
        obtain ⟨spent, kept, safe⟩ := stepRun
        change state.clock - 1 ≤ middle.clock + cost at spent
        change middle.clock ≤ state.clock - 1 at kept
        have oneIteration : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
        cases result with
        | none =>
          dsimp only
          have adv := advance (decClockHOLFinite state) w pclock atClock (by rw [bodyRun])
          obtain ⟨nextCounter, nextCode⟩ := adv
          have nextCounter' : middle.locals.lookup counter = some (.val (.word (w + step))) := by
            simpa [bodyRun] using nextCounter
          have nextCode' : middle.code = (decClockHOLFinite state).code := by
            simpa [bodyRun] using nextCode
          have keepP : P middle := by
            simpa [bodyRun] using keep (decClockHOLFinite state) w pclock codeClock atClock
              (by rw [bodyRun])
          have natural : (w + step).toNat = w.toNat + step.toNat := BitVec.toNat_add_of_lt (by omega)
          have nextRank : K.toNat - (w + step).toNat < n := by rw [natural]; omega
          have tail := ih (K.toNat - (w + step).toNat) nextRank middle keepP (nextCode'.trans codeClock) (w + step)
            nextCounter' (by rw [natural]; omega) rfl (by
              have : (K.toNat - (w + step).toNat) * (cost + 1) + (cost + 1) ≤ n * (cost + 1) := by
                rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
              omega)
          obtain ⟨t1, t2, t3⟩ := tail
          refine ⟨?_, by omega, t3⟩
          have : (K.toNat - (w + step).toNat) * (cost + 1) + (cost + 1) ≤ n * (cost + 1) := by
            rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
          omega
        | some r =>
          cases r with
          | «continue» =>
            have hc : (evaluateHOLFiniteState (decClockHOLFinite state) body).1 = some .continue := by
              rw [bodyRun]
            exact absurd hc (noContinue (decClockHOLFinite state) w pclock)
          | «break» => exact ⟨by simp; omega, by simp; omega, by simp⟩
          | timeOut => exact absurd rfl safe
          | _ => exact ⟨by simp; omega, by simp; omega, by simp⟩
    · rw [if_neg lt]
      simp


/-- **Per-iteration clock bound of statement 46.** One iteration runs the actual installed
withdrawal encoder through `decCall` and then the two straight-line slice stores, so it spends
`encodeWithdrawalSourceCost DF + 1` ticks in every outcome (including a failed allocator inside the
encoder), with no future-room or oracle assumption: the premises are the real heap/fence bounds at
the iteration state. -/
theorem wdSliceLoopBody_runBounded {F : Type} (t : PanSemStateFiniteExact 64 F)
    (argumentWord heap : BitVec 64) (DF : Nat)
    (hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
      [.op .add [.load .one (.op .add [.var .local (ofString "pl"), .const (48#64)]),
        .panop .mul [.var .local (ofString "i"), .const (44#64)]]] =
      some [ValueHOL.val (HolWordLab.word argumentWord)])
    (code : t.code = originalRuntimeCode) (fence : Fence t.memaddrs DF) (cap : DF + 8 ≤ 2^62)
    (heapFence : 33806089496 ≤ DF)
    (atHeap : t.globals.lookup (ofString "heap_ptr") = some (ValueHOL.val (HolWordLab.word heap)))
    (heapCap : heap.toNat ≤ 33806089496)
    (budget : encodeWithdrawalSourceCost DF + 1 ≤ t.clock) :
    RunBounded t wdSliceLoopBody (encodeWithdrawalSourceCost DF + 1) := by
  rw [wdSliceLoopBody]
  refine RunBounded.decCall (bodyCost := encodeWithdrawalSourceCost DF) (tailCost := 0) hargs budget ?_
  intro body locals returnShape lookup
  have bodyRun := encode_withdrawal_body_bounded (callEntryStateHOLFinite t locals) heap DF code
    fence cap heapFence atHeap heapCap (by change encodeWithdrawalSourceCost DF ≤ t.clock - 1; omega)
  generalize hinst : (sourceFunctionBody Guest.guestFn_encode_withdrawal_rlp) = installedBody at bodyRun
  have same : body = installedBody := by
    have found := lookupCodeHOLFinite_installed_body t.code.lookup (ofString "encode_withdrawal_rlp")
      [(ofString "wd", ShapeHOL.one)] (sourceFunctionBody Guest.guestFn_encode_withdrawal_rlp) body
      (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one]) returnShape _
      locals (by rw [code]; exact originalRuntimeCode_encodeWithdrawal_lookup) lookup
    exact found.trans hinst
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · exact same ▸ bodyRun.1
  · exact same ▸ bodyRun.2.1
  · exact same ▸ bodyRun.2.2
  · intro value post returned tailBudget
    exact runBounded_zero_of_extStraightLine
      (state := setVarHOLFinite (ofString "e") value { post with locals := t.locals })
      wdSliceLoopStores wdSliceLoopStores_extStraightLine


/-- **Statement-46 loop runtime bound.** The withdrawal slice loop `while i < nwd` of
`actualPayloadHeaderAt 46` runs at most `nwd - i` iterations, each costing one condition tick plus one
iteration of `wdSliceLoopBody`, i.e. `encodeWithdrawalSourceCost DF + 2` ticks; the per-iteration
encoder cost is the real installed encoder bound, so the total `nwd.toNat * (cost + 1)` is a genuine
source bound with no future-runtime oracle. The state predicate `P` is the loop invariant carrying the
decoder bindings, the heap frontier and the fence; the caller supplies its preservation, which is the
only remaining obligation. -/
theorem wdSliceLoop_runBounded (DF : Nat) (nwd : BitVec 64)
    (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (run : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (w : BitVec 64), P state →
      state.code = originalRuntimeCode →
      state.locals.lookup (ofString "i") = some (.val (.word w)) →
      encodeWithdrawalSourceCost DF + 1 ≤ state.clock →
      RunBounded state wdSliceLoopBody (encodeWithdrawalSourceCost DF + 1))
    (keep : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (w : BitVec 64), P state →
      state.code = originalRuntimeCode →
      state.locals.lookup (ofString "i") = some (.val (.word w)) →
      (evaluateHOLFiniteState state wdSliceLoopBody).1 = none → P (evaluateHOLFiniteState state wdSliceLoopBody).2)
    (advance : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (w : BitVec 64), P state →
      state.locals.lookup (ofString "i") = some (.val (.word w)) →
      (evaluateHOLFiniteState state wdSliceLoopBody).1 = none →
      (evaluateHOLFiniteState state wdSliceLoopBody).2.locals.lookup (ofString "i") =
        some (.val (.word (w + 1#64))) ∧
      (evaluateHOLFiniteState state wdSliceLoopBody).2.code = state.code)
    (noContinue : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (w : BitVec 64), P state →
      (evaluateHOLFiniteState state wdSliceLoopBody).1 ≠ some .continue)
    (decrease : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), P state → P (decClockHOLFinite state))
    (atBound : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), P state →
      state.locals.lookup (ofString "nwd") = some (.val (.word nwd)))
    (small : nwd.toNat + 1 < 2 ^ 63) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), P state →
      state.code = originalRuntimeCode →
      ∀ I0 : BitVec 64, state.locals.lookup (ofString "i") = some (.val (.word I0)) →
      I0.toNat ≤ nwd.toNat + 1 → nwd.toNat - I0.toNat = n →
      n * ((encodeWithdrawalSourceCost DF + 1) + 1) ≤ state.clock →
      state.clock ≤ (evaluateHOLFiniteState state wdSliceLoop).2.clock +
        n * ((encodeWithdrawalSourceCost DF + 1) + 1) ∧
        (evaluateHOLFiniteState state wdSliceLoop).2.clock ≤ state.clock ∧
        (evaluateHOLFiniteState state wdSliceLoop).1 ≠ some .timeOut := by
  intro n
  have hop : (Cmp.less : Cmp) = .less ∨ (Cmp.less : Cmp) = .lower := Or.inl rfl
  have small' : nwd.toNat + (1#64).toNat < 2 ^ 63 := by
    have : (1#64).toNat = 1 := by decide
    omega
  have positive : 0 < (1#64).toNat := by decide
  intro F state pstate code0 I0 atCounter0 within0 distance0 budget0
  exact countedWhile_runBounded_var (counter := ofString "i") (bound := ofString "nwd")
    (op := .less) (hop := hop) (K := nwd) (step := 1#64) (small := small') (positive := positive)
    (body := wdSliceLoopBody) (cost := encodeWithdrawalSourceCost DF + 1)
    (P := P) run keep advance noContinue decrease atBound n
    state pstate code0 I0 atCounter0 within0 distance0 budget0

#print axioms wdSliceLoop_runBounded
#print axioms countedWhile_runBounded_var

#print axioms wdSliceLoopBody_runBounded

#print axioms countedWhile_runBounded
end InitECandidate.Runtime
