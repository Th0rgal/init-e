import InitECandidate.Runtime.SszCheckOffsetsInner
import InitECandidate.Runtime.SszCheckOffsetsSource
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Returned contract of ssz_check_offsets: return value 0, every offset
accepted (in [fixed,len], nondecreasing), and offs[0] = fixed when n ≠ 0. -/
def SszCheckOffsetsReturned {σ : Type} (e : PanSemStateFiniteExact 64 σ) (offs n fixed len : BitVec 64)
    (v : ValueHOL 64) : Prop :=
  v = .val (.word 0) ∧ (∀ k : BitVec 64, k.toNat < n.toNat → SszOffsetOK e offs fixed len k) ∧
    (n ≠ 0 → e.memaddrs offs ∧ memWord e.memory offs = fixed)

theorem evaluate_sszCheckOffsets_body_enough {σ : Type} (e : PanSemStateFiniteExact 64 σ)
    (offs n fixed len : BitVec 64) (installed : e.code = originalRuntimeCode)
    (hoffs : e.locals.lookup (ofString "offs") = some (.val (.word offs)))
    (hn : e.locals.lookup (ofString "n") = some (.val (.word n)))
    (hfixed : e.locals.lookup (ofString "fixed") = some (.val (.word fixed)))
    (hlen : e.locals.lookup (ofString "len") = some (.val (.word len)))
    (small : n.toNat < 2 ^ 63) (enough : 2 * n.toNat + 1 ≤ e.clock) :
    let out := evaluateHOLFiniteState e (sourceFunctionBody Guest.guestFn_ssz_check_offsets)
    e.clock ≤ out.2.clock + (2 * n.toNat + 1) ∧ out.2.clock ≤ e.clock ∧ out.1 ≠ none ∧ out.1 ≠ some .timeOut ∧
      (∀ v, out.1 = some (.returned v) → SszCheckOffsetsReturned e offs n fixed len v) := by
  rw [source_sszCheckOffsets_body, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  by_cases zero : n = 0
  · subst zero
    have cond : @evalHOLExact 64 σ _ e.toExact (fun a => Classical.propDecidable (e.memaddrs a))
        (.cmp .equal (.var .local (ofString "n")) (.const 0)) = some (.val (.word 1#64)) := by
      simp [evalHOLExact, hn, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [cond]
    simp [evalHOLExact, shapeOfHOLExact, emptyLocalsHOLFinite, SszCheckOffsetsReturned]
  · have cond : @evalHOLExact 64 σ _ e.toExact (fun a => Classical.propDecidable (e.memaddrs a))
        (.cmp .equal (.var .local (ofString "n")) (.const 0)) = some (.val (.word 0#64)) := by
      simp [evalHOLExact, hn, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      exact zero
    rw [cond]
    dsimp only
    rw [if_pos (show (0#64 : BitVec 64) = 0 from rfl), evaluateHOLFiniteState_skip]
    dsimp only
    rw [evaluateHOLFiniteState_dec_total]
    simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true]
    let q := setVarHOLFinite (ofString "i") (.val (.word 0#64)) e
    obtain ⟨_, _, _, _, _, n6, n7, n8, n9⟩ := sszcheck_names
    have up : ∀ k, k ≠ ofString "i" → q.locals.lookup k = e.locals.lookup k := by
      intro k hk; simp [q, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk, hk]
    have qi : q.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
      simp [q, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have inner := evaluate_sszCheckInner q offs n fixed len installed ((up _ (Ne.symm n6)).trans hoffs)
      ((up _ (Ne.symm n7)).trans hn) ((up _ (Ne.symm n8)).trans hfixed) ((up _ (Ne.symm n9)).trans hlen) qi
      small enough
    change (let out := (let o := evaluateHOLFiniteState q (.seq sszCheckLoop sszCheckFinal);
      (o.1, {o.2 with locals := o.2.locals.resVarEq (ofString "i", e.locals.lookup (ofString "i"))})); _)
    cases run : evaluateHOLFiniteState q (.seq sszCheckLoop sszCheckFinal) with
    | mk r post =>
      rw [run] at inner
      dsimp only at inner ⊢
      obtain ⟨i1, i2, i3, i4, i5⟩ := inner
      refine ⟨i1, i2, i3, i4, fun v h => ?_⟩
      obtain ⟨rfl, all, dom, eq⟩ := i5 v h
      exact ⟨rfl, all, fun _ => ⟨dom, eq⟩⟩

/-- The actual ssz_check_offsets body at any clock: at most 2n+1 clocks,
no timeout with that much clock, and every return satisfies the contract. -/
theorem evaluate_sszCheckOffsets_body {σ : Type} (e : PanSemStateFiniteExact 64 σ)
    (offs n fixed len : BitVec 64) (installed : e.code = originalRuntimeCode)
    (hoffs : e.locals.lookup (ofString "offs") = some (.val (.word offs)))
    (hn : e.locals.lookup (ofString "n") = some (.val (.word n)))
    (hfixed : e.locals.lookup (ofString "fixed") = some (.val (.word fixed)))
    (hlen : e.locals.lookup (ofString "len") = some (.val (.word len)))
    (small : n.toNat < 2 ^ 63) :
    let out := evaluateHOLFiniteState e (sourceFunctionBody Guest.guestFn_ssz_check_offsets)
    e.clock ≤ out.2.clock + (2 * n.toNat + 1) ∧ out.2.clock ≤ e.clock ∧
      (2 * n.toNat + 1 ≤ e.clock → out.1 ≠ some .timeOut) ∧ out.1 ≠ none ∧
      (∀ v, out.1 = some (.returned v) → SszCheckOffsetsReturned e offs n fixed len v) := by
  by_cases enough : 2 * n.toNat + 1 ≤ e.clock
  · obtain ⟨a, b, c, d, f⟩ := evaluate_sszCheckOffsets_body_enough e offs n fixed len installed hoffs hn hfixed hlen
      small enough
    exact ⟨a, b, fun _ => d, c, f⟩
  · intro out
    have lower := evaluateHOLFiniteState_clock_le e (sourceFunctionBody Guest.guestFn_ssz_check_offsets)
    let lifted : PanSemStateFiniteExact 64 σ := {e with clock := e.clock + (2 * n.toNat + 1)}
    have high := evaluate_sszCheckOffsets_body_enough lifted offs n fixed len installed hoffs hn hfixed hlen
      small (by simp [lifted])
    have transfer : out.1 ≠ some .timeOut →
        (evaluateHOLFiniteState lifted (sourceFunctionBody Guest.guestFn_ssz_check_offsets)).1 = out.1 := by
      intro nt
      have same := panPropsEvaluateAddClockEq (sourceFunctionBody Guest.guestFn_ssz_check_offsets) e out.1 out.2
        (2 * n.toNat + 1) ⟨rfl, nt⟩
      change (evaluateHOLFiniteState {e with clock := e.clock + (2 * n.toNat + 1)} _).1 = _
      rw [same]
    refine ⟨by omega, lower, fun h => absurd h enough, ?_, ?_⟩
    · intro none_
      exact high.2.2.1 ((transfer (by rw [none_]; simp)).trans none_)
    · intro v returned
      exact high.2.2.2.2 v ((transfer (by rw [returned]; simp)).trans returned)

#print axioms evaluate_sszCheckOffsets_body_enough
#print axioms evaluate_sszCheckOffsets_body
end InitECandidate.Runtime
