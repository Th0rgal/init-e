import InitECandidate.Runtime.StatelessPrefixSource
import InitECandidate.Runtime.SszCheckOffsetsCallBound
import InitECandidate.Runtime.SszCheckOffsetsCallReturned
import InitECandidate.Runtime.SszFailCallBound
import InitECandidate.Runtime.SszFailCallTerminal
import InitECandidate.Runtime.SszFailCallNoReturn
import InitECandidate.Runtime.SszSplitVarListEval
import InitECandidate.Runtime.DiscardCallNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A terminal non-returning prefix outcome within K ticks (timeout-free with K ticks). -/
def StAbort {σ : Type} (s : PanSemStateFiniteExact 64 σ) (out : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ)
    (K : Nat) : Prop :=
  ∃ x, out.1 = some x ∧ (∀ v, x ≠ .returned v) ∧ s.clock ≤ out.2.clock + K ∧ out.2.clock ≤ s.clock ∧
    (K ≤ s.clock → x ≠ .timeOut)

theorem stAbort_mono {σ : Type} (s : PanSemStateFiniteExact 64 σ) out (K K' : Nat) (le : K ≤ K')
    (h : StAbort s out K) : StAbort s out K' := by
  obtain ⟨x, h1, h2, h3, h4, h5⟩ := h
  exact ⟨x, h1, h2, by omega, h4, fun k => h5 (by omega)⟩

theorem stAbort_seq {σ : Type} (s : PanSemStateFiniteExact 64 σ) (first rest : ProgHOL 64) (K : Nat)
    (h : StAbort s (evaluateHOLFiniteState s first) K) : StAbort s (evaluateHOLFiniteState s (.seq first rest)) K := by
  obtain ⟨x, h1, h2, h3, h4, h5⟩ := h
  rw [evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState s first with
  | mk r t =>
    rw [run] at h1 h3 h4
    dsimp only at h1 h3 h4 ⊢
    subst h1
    exact ⟨x, rfl, h2, h3, h4, h5⟩

theorem stAbort_error {σ : Type} (s : PanSemStateFiniteExact 64 σ) (K : Nat) : StAbort s (some .error, s) K :=
  ⟨.error, rfl, by simp, by simp, Nat.le_refl _, fun _ => by simp⟩

theorem stFail_abort {σ : Type} (s : PanSemStateFiniteExact 64 σ) (c : BitVec 64) (code : s.code = originalRuntimeCode) :
    StAbort s (evaluateHOLFiniteState s (stFail c)) 1 := by
  have args : evalListHOLFinite s (h := fun address => Classical.propDecidable (s.memaddrs address))
      [.const c] = some [.val (.word c)] := by simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have terminal := evaluate_sszFail_call_terminal s (.const c) c code args
  have lower := evaluateHOLFiniteState_clock_le s (stFail c)
  unfold stFail at lower ⊢
  cases run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "ssz_fail") [.const c]) with
  | mk r t =>
    rw [run] at terminal lower
    dsimp only at terminal lower ⊢
    cases r with
    | none => exact absurd rfl terminal
    | some x =>
      refine ⟨x, rfl, fun v h => ?_, ?_, lower, fun pos => ?_⟩
      · have nr := evaluate_sszFail_call_no_return s (.const c) c v code args
        rw [run] at nr; exact nr (by rw [h])
      · by_cases zero : s.clock = 0
        · omega
        · have b := evaluate_sszFail_call_bounded s (.const c) c code zero args
          rw [run] at b
          obtain ⟨b1, _, _⟩ := b
          have b1' : t.clock = s.clock - 1 := b1
          omega
      · have b := evaluate_sszFail_call_bounded s (.const c) c code (by omega) args
        rw [run] at b
        obtain ⟨_, b2, _⟩ := b
        simp only at b2
        exact fun h => b2 (by rw [h])

/-- A guard either passes (condition evaluates to 0, state unchanged) or aborts within one tick. -/
theorem stGuard_cases {σ : Type} (s : PanSemStateFiniteExact 64 σ) (cond : ExpHOL 64) (c : BitVec 64)
    (code : s.code = originalRuntimeCode) :
    (@evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond = some (.val (.word 0)) ∧
      evaluateHOLFiniteState s (.ite cond (stFail c) .skip) = (none, s)) ∨
    StAbort s (evaluateHOLFiniteState s (.ite cond (stFail c) .skip)) 1 := by
  rw [evaluateHOLFiniteState_ite]
  split
  · rename_i w hw
    split
    · rename_i zero
      subst zero
      exact Or.inl ⟨hw, by rw [evaluateHOLFiniteState_skip]⟩
    · exact Or.inr (stFail_abort s c code)
  · exact Or.inr (stAbort_error s 1)

/-- A word store at a known address either writes it (cell in the domain) or aborts. -/
theorem stStore_cases {σ : Type} (s : PanSemStateFiniteExact 64 σ) (dest e : ExpHOL 64) (a : BitVec 64)
    (hd : @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) dest = some (.val (.word a)))
    (bounded : @Bounded32 σ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e) :
    (∃ x : BitVec 64, x.toNat < 2 ^ 32 ∧ s.memaddrs a ∧
      evaluateHOLFiniteState s (.store dest e) = (none, {s with memory := wmem s.memory a x})) ∨
    StAbort s (evaluateHOLFiniteState s (.store dest e)) 0 := by
  cases hv : @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e with
  | none =>
    right
    rw [evaluateHOLFiniteState_store, hd]
    simp only [hv]
    exact stAbort_error s 0
  | some v =>
    obtain ⟨x, rfl, small⟩ := bounded _ hv
    by_cases dom : s.memaddrs a
    · exact Or.inl ⟨x, small, dom, sszStore_in s a x dest e hd hv dom⟩
    · right; rw [sszStore_out s a x dest e hd hv dom]; exact stAbort_error s 0

end InitECandidate.Runtime
