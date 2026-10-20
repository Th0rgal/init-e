import InitECandidate.Runtime.WordExecutionCostProps
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 2000000
/-- Local work components add over the same executed call/loop path. -/
theorem wordExecutionCost_add {width : Nat} [NeZero width] {C F : Type}
    (left right : WordLangProgHOL (BitVec width) → WordSemStateFiniteExact width C F → Nat)
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    wordExecutionCost (fun p s => left p s + right p s) p s =
      wordExecutionCost left p s + wordExecutionCost right p s := by
  classical
  fun_induction wordExecutionCost left p s <;> (try simp_all +zetaDelta [wordExecutionCost])
  case case3 =>
    rename_i state comparison register operand first second ihFirst ihSecond
    cases hx : getVar register state <;>
      cases hy : WordSemStateFiniteExact.getVarImm operand state <;> simp only [hx, hy]
    all_goals try omega
    rename_i x y
    cases hc : wordSemWordCmp comparison x y with
    | none => simp only [hx, hy, hc]; omega
    | some choice => cases choice <;> simp only [hx, hy, hc] <;> omega
  all_goals try omega
  all_goals try (split <;> (try simp_all only [ite_true, ite_false]) <;> (try omega))
  all_goals try (split <;> (try simp_all only [ite_true, ite_false]) <;> (try omega))
  all_goals grind (splits := 40) only

/-- Scaling local prices scales the actual path work once, independently of
call depth or loop nesting. -/
theorem wordExecutionCost_scale {width : Nat} [NeZero width] {C F : Type}
    (price : WordLangProgHOL (BitVec width) → WordSemStateFiniteExact width C F → Nat)
    (coefficient : Nat) (p : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) :
    wordExecutionCost (fun p s => coefficient * price p s) p s =
      coefficient * wordExecutionCost price p s := by
  induction coefficient with
  | zero => simpa only [Nat.zero_mul] using wordExecutionCost_zero p s
  | succ coefficient ih =>
    simpa only [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul,
      wordExecutionCost_add, ih]

/-- A pointwise compiler price envelope transfers to an execution envelope
without multiplying at recursive calls or nested loops. Each component is
charged along exactly the same actual execution. -/
theorem wordExecutionCost_linear_envelope {width : Nat} [NeZero width] {C F : Type}
    (actual first second : WordLangProgHOL (BitVec width) → WordSemStateFiniteExact width C F → Nat)
    (a b : Nat)
    (prices : ∀ p s, actual p s ≤ a * first p s + b * second p s)
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    wordExecutionCost actual p s ≤
      a * wordExecutionCost first p s + b * wordExecutionCost second p s := by
  have bound := wordExecutionCost_mono actual
    (fun p s => a * first p s + b * second p s) prices p s
  simpa only [wordExecutionCost_add, wordExecutionCost_scale] using bound

#print axioms wordExecutionCost_linear_envelope
#print axioms wordExecutionCost_scale
#print axioms wordExecutionCost_add
end InitECandidate.Runtime.FineCost
