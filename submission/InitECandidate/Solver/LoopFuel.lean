import Init

/-!
# Op 3: abstract loop-fuel lemmas (ranking-function form)

Semantics-agnostic. This is the arithmetic used to bound the source clock of a
`while` loop in the software guest. It is not yet tied to
`PanSemStateFiniteExact`: the bridge to `whileStepHOLExact` is the next
obligation (see `OP3_MAXWELL_REPORT.md`).

A loop is modelled as a partial step `step : α → Option α` (`none` = exit).
A ranking `μ` that strictly decreases on every continuing step bounds the
number of iterations by `μ s₀`; the fuel is then `μ s₀ * (body + 1) + 1`.
-/

namespace InitECandidate.Solver.LoopFuel

variable {α : Type}

/-- Run at most `n` iterations; `some s` when the loop has not exited yet. -/
def iterate (step : α → Option α) : Nat → α → Option α
  | 0, s => some s
  | n + 1, s => match step s with
    | none => none
    | some s' => iterate step n s'

/-- With a strictly decreasing ranking, the loop has exited after `μ s + 1` iterations. -/
theorem exits_within (step : α → Option α) (μ : α → Nat)
    (dec : ∀ s s', step s = some s' → μ s' < μ s) :
    ∀ s, iterate step (μ s + 1) s = none := by
  intro s
  suffices H : ∀ n s, μ s < n → iterate step n s = none from H _ s (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro s h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro s h
    simp only [iterate]
    rcases hs : step s with _ | s'
    · rfl
    · exact ih s' (by have := dec s s' hs; omega)

/-- Clock charged by a loop whose body costs at most `body` ticks and whose
guard check costs one tick, given a ranking bound `μ s ≤ M`. -/
def loopFuel (M body : Nat) : Nat := (M + 1) * (body + 1)

theorem loopFuel_mono {M M' b b' : Nat} (hM : M ≤ M') (hb : b ≤ b') :
    loopFuel M b ≤ loopFuel M' b' :=
  Nat.mul_le_mul (Nat.add_le_add_right hM 1) (Nat.add_le_add_right hb 1)

/-- Nested loops: the inner fuel becomes the outer body cost. -/
theorem nested_loopFuel (Mo Mi b : Nat) :
    loopFuel Mo (loopFuel Mi b) = (Mo + 1) * ((Mi + 1) * (b + 1) + 1) := rfl

/-- Counter loop `while i < n { i := i + d }` with `d ≥ 1`: ranking `n - i`. -/
theorem counter_loop_exits (n d : Nat) (hd : 1 ≤ d) (i : Nat) :
    iterate (fun j => if j < n then some (j + d) else none) (n - i + 1) i = none :=
  exits_within _ (fun j => n - j) (by
    intro j j' h
    by_cases hj : j < n
    · simp [hj] at h; subst h; omega
    · simp [hj] at h) i

/-- Decrement loop `while i > 0 { i := i - 1 }`: ranking `i`. -/
theorem decrement_loop_exits (i : Nat) :
    iterate (fun j => if 0 < j then some (j - 1) else none) (i + 1) i = none :=
  exits_within _ id (by
    intro j j' h
    by_cases hj : 0 < j
    · simp [hj] at h; subst h; simp; omega
    · simp [hj] at h) i

end InitECandidate.Solver.LoopFuel
