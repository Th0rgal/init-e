import InitECandidate.Runtime.CrepFfiBudget
namespace InitECandidate.Runtime
open Flapjack

set_option maxHeartbeats 2000000

private theorem classicalFun_eq {width : Nat} [NeZero width] {F : Type}
    (s : CrepSemHOLState width F) : crepExactEvalExpClassical s = evalCrepSemHOLExp s :=
  funext (crepExactEvalExpClassical_eq s)

private theorem lookupCodeFinite_eq_HOLFinite' {width : Nat} [NeZero width]
    (c : HolFiniteMapExact Flapjack.Basis.Pure.MlString.MlString (List Nat × CrepProgHOL width))
    (f : Flapjack.Basis.Pure.MlString.MlString) (args : List (HolWordLab width)) (len : Nat) :
    lookupCodeFiniteHOL c f args len = lookupCodeHOLFinite c.lookup f args len := by
  have h1 := lookupCodeFiniteHOL_lookup c f args len
  unfold lookupCodeHOLFinite
  split
  · rename_i hn
    rw [hn] at h1
    cases hF : lookupCodeFiniteHOL c f args len with
    | none => rfl
    | some val => rw [hF] at h1; simp at h1
  · rename_i body cl hs
    rw [hs] at h1
    cases hF : lookupCodeFiniteHOL c f args len with
    | none => rw [hF] at h1; simp at h1
    | some val =>
        obtain ⟨b, m⟩ := val
        rw [hF] at h1
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, hm⟩ := h1
        congr 2
        exact holFiniteMapExact_eq_of_lookup_eq hm

/-- Crep has no dynamic code installation: execution preserves its code table. -/
theorem crep_evaluate_code {width : Nat} [NeZero width] {F : Type}
    (p : CrepProgHOL width) (s : CrepSemHOLState width F) :
    (evalCrepSemHOLProgExact s p).2.code = s.code := by
  apply evalCrepSemHOLProgExact_induct
    (P := fun x => (evalCrepSemHOLProgExact x.2 x.1).2.code = x.2.code)
  case hite =>
    intro e yes no state ih
    rw [evalCrepSemHOLProgExact_eq_evaluate_def]
    dsimp only
    cases found : evalCrepSemHOLExp state e with
    | none => rfl
    | some value =>
      cases value with
      | word w =>
        have h := ih (.word w) w (by simpa only [classicalFun_eq] using found) rfl
        simpa only [ite_not] using h
  all_goals intros
  all_goals rw [evalCrepSemHOLProgExact_eq_evaluate_def]
  all_goals dsimp only
  all_goals try simp only [classicalFun_eq, ← lookupCodeFinite_eq_HOLFinite'] at *
  all_goals repeat' first | rfl | (dsimp only at *) | split
  all_goals try simp_all [decClockCrepSemHOL, CrepSemHOLState.setVar, CrepSemHOLState.emptyLocals]
  all_goals try grind
  all_goals simp only [crepShMemOpExactHOL]
  all_goals split <;> simp only [crepShMemLoadExactHOL, crepShMemStoreExactHOL, CrepSemHOLState.setVar]
  all_goals repeat' first | rfl | (dsimp only) | split



/-- Uniform source procedure-size ceiling, preserved across every execution. -/
def CrepCodeSize {width : Nat} [NeZero width] {F : Type}
    (limit : Nat) (s : CrepSemHOLState width F) : Prop :=
  ∀ name params body, s.code.lookup name = some (params,body) → sizeOf body ≤ limit

theorem CrepCodeSize.of_code_eq {width : Nat} [NeZero width] {F : Type}
    {limit : Nat} {s next : CrepSemHOLState width F}
    (bounded : CrepCodeSize limit s) (same : next.code = s.code) : CrepCodeSize limit next := by
  intro name params body found
  rw [same] at found
  exact bounded name params body found

theorem CrepCodeSize.evaluated {width : Nat} [NeZero width] {F : Type}
    {limit : Nat} {s : CrepSemHOLState width F} (bounded : CrepCodeSize limit s)
    (p : CrepProgHOL width) : CrepCodeSize limit (evalCrepSemHOLProgExact s p).2 :=
  bounded.of_code_eq (crep_evaluate_code p s)

theorem CrepCodeSize.decClock {width : Nat} [NeZero width] {F : Type}
    {limit : Nat} {s : CrepSemHOLState width F} (bounded : CrepCodeSize limit s) :
    CrepCodeSize limit (decClockCrepSemHOL s) := bounded.of_code_eq rfl

theorem CrepCodeSize.setLocals {width : Nat} [NeZero width] {F : Type}
    {limit : Nat} {s : CrepSemHOLState width F} (bounded : CrepCodeSize limit s)
    (locals : HolFiniteMapExact Nat (HolWordLab width)) :
    CrepCodeSize limit {s with locals := locals} := bounded.of_code_eq rfl

theorem CrepCodeSize.lookup {width : Nat} [NeZero width] {F : Type}
    {limit : Nat} {s : CrepSemHOLState width F} (bounded : CrepCodeSize limit s)
    (name : Flapjack.Basis.Pure.MlString.MlString) (args : List (HolWordLab width))
    (body : CrepProgHOL width) (locals : HolFiniteMapExact Nat (HolWordLab width))
    (found : lookupCodeFiniteHOL s.code name args args.length = some (body,locals)) :
    sizeOf body ≤ limit := by
  unfold lookupCodeFiniteHOL at found
  cases entry : s.code.lookup name with
  | none => simp [entry] at found
  | some pair =>
    rcases pair with ⟨params,program⟩
    by_cases guard : params.length = args.length ∧ params.Nodup
    · simp only [entry,if_pos guard,Option.some.injEq,Prod.mk.injEq] at found
      rw [← found.1]
      exact bounded name params program entry
    · simp [entry,guard] at found

#print axioms CrepCodeSize.lookup
#print axioms CrepCodeSize.evaluated
#print axioms crep_evaluate_code
end InitECandidate.Runtime
