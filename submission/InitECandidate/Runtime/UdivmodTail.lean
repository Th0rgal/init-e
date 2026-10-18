import InitECandidate.Runtime.UdivmodLoopRun
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Initial loop state after the three actual declarations. -/
def udivTailEntry {σ : Type} (t : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  setVarHOLFinite (ofString "i") (.val (.word 64))
    (setVarHOLFinite (ofString "r") (.val (.word 0)) (setVarHOLFinite (ofString "q") (.val (.word 0)) t))

theorem udivTailEntry_inv {σ : Type} (t : PanSemStateFiniteExact 64 σ) (a b : BitVec 64)
    (ha : t.locals.lookup (ofString "a") = some (.val (.word a)))
    (hb : t.locals.lookup (ofString "b") = some (.val (.word b))) (nz : b ≠ 0) :
    UdivLoopInv t a b (udivTailEntry t) ∧ udivLoopRank (udivTailEntry t) = 64 := by
  obtain ⟨n1,n2,n3,n4,n5,n6,n7,n8,n9⟩ := udiv_names
  have pos : 0 < b.toNat := by
    have : b.toNat ≠ 0 := fun e => nz (BitVec.eq_of_toNat_eq (by simp [e])); omega
  have hiLookup : (udivTailEntry t).locals.lookup (ofString "i") = some (.val (.word 64)) := by
    simp [udivTailEntry, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  refine ⟨⟨0, 0, 64, (udivTailEntry t).locals, rfl, ?_, ?_, ?_, ?_, hiLookup, by decide,
    by simpa using udivInv_initial a b pos⟩, by simp [udivLoopRank, hiLookup]⟩
  all_goals simp [udivTailEntry, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, n1, n2, n3, n4, n5,
    n6, n7, n8, n9, Ne.symm n1, Ne.symm n2, Ne.symm n3, Ne.symm n4, Ne.symm n5, Ne.symm n6, Ne.symm n7,
    Ne.symm n8, Ne.symm n9, ha, hb]

#print axioms udivTailEntry_inv

theorem udivInv_zero_values {σ : Type} {base : PanSemStateFiniteExact 64 σ} {a b : BitVec 64}
    {post : PanSemStateFiniteExact 64 σ} (inv : UdivLoopInv base a b post) (zero : udivLoopRank post = 0) :
    post.locals.lookup (ofString "q") = some (.val (.word (a / b))) ∧
    post.locals.lookup (ofString "r") = some (.val (.word (a % b))) := by
  obtain ⟨q, r, i, L, shape, ha, hb, hq, hr, hi, bound, arith⟩ := inv
  have hs : ∀ name, post.locals.lookup name = L.lookup name := by intro name; rw [shape]
  have rank : udivLoopRank post = i.toNat := by simp [udivLoopRank, hs, hi]
  rw [rank] at zero
  rw [zero] at arith
  obtain ⟨hqn, hrn⟩ := udivInv_final arith
  have qe : q = a / b := BitVec.eq_of_toNat_eq (by rw [hqn, BitVec.toNat_udiv])
  have re : r = a % b := BitVec.eq_of_toNat_eq (by rw [hrn, BitVec.toNat_umod])
  rw [hs, hs, hq, hr, qe, re]
  exact ⟨rfl, rfl⟩

/-- The actual declaration/loop/return tail: at most 64 clocks, no timeout
with 64 clocks available, and any returned value is the exact quotient and remainder. -/
theorem evaluate_udivmodTail_enough {σ : Type} (t : PanSemStateFiniteExact 64 σ) (a b : BitVec 64)
    (ha : t.locals.lookup (ofString "a") = some (.val (.word a)))
    (hb : t.locals.lookup (ofString "b") = some (.val (.word b))) (nz : b ≠ 0) (enough : 64 ≤ t.clock) :
    let out := evaluateHOLFiniteState t udivmodTail
    t.clock ≤ out.2.clock + 64 ∧ out.2.clock ≤ t.clock ∧ (64 ≤ t.clock → out.1 ≠ some .timeOut) ∧
      (∀ value, out.1 = some (.returned value) →
        value = .rStruct [.val (.word (a / b)), .val (.word (a % b))]) := by
  obtain ⟨inv, rank⟩ := udivTailEntry_inv t a b ha hb nz
  simp only [udivmodTail, evaluateHOLFiniteState_dec_total, evaluateHOLFiniteState_seq_line780]
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true]
  have entryEq : setVarHOLFinite (ofString "i") (.val (.word 64))
      (setVarHOLFinite (ofString "r") (.val (.word 0)) (setVarHOLFinite (ofString "q") (.val (.word 0)) t)) =
      udivTailEntry t := rfl
  rw [entryEq]
  have entryClock : (udivTailEntry t).clock = t.clock := rfl
  · obtain ⟨result, post, run, c1, c2, noTimeout, done, noReturn⟩ :=
      evaluate_udivmodLoop t a b (udivTailEntry t) inv (by rw [rank, entryClock]; exact enough)
    rw [run]
    rw [rank, entryClock] at c1
    rw [entryClock] at c2
    cases result with
    | none =>
      obtain ⟨postInv, postZero⟩ := done rfl
      obtain ⟨hq, hr⟩ := udivInv_zero_values postInv postZero
      simp [evaluateHOLFiniteState_return, evalHOLExact, evalListHOLExact, toExact, hq, hr, shapeOfHOLExact,
        Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL, emptyLocalsHOLFinite]
      omega
    | some value =>
      simp only
      refine ⟨by omega, by omega, fun _ => noTimeout, ?_⟩
      intro returned equal
      exact absurd equal (noReturn returned)

theorem evaluate_udivmodTail {σ : Type} (t : PanSemStateFiniteExact 64 σ) (a b : BitVec 64)
    (ha : t.locals.lookup (ofString "a") = some (.val (.word a)))
    (hb : t.locals.lookup (ofString "b") = some (.val (.word b))) (nz : b ≠ 0) :
    let out := evaluateHOLFiniteState t udivmodTail
    t.clock ≤ out.2.clock + 64 ∧ out.2.clock ≤ t.clock ∧ (64 ≤ t.clock → out.1 ≠ some .timeOut) ∧
      (∀ value, out.1 = some (.returned value) →
        value = .rStruct [.val (.word (a / b)), .val (.word (a % b))]) := by
  by_cases enough : 64 ≤ t.clock
  · exact evaluate_udivmodTail_enough t a b ha hb nz enough
  · intro out
    have lower := evaluateHOLFiniteState_clock_le t udivmodTail
    refine ⟨by omega, lower, fun h => absurd h enough, ?_⟩
    intro value returned
    let lifted : PanSemStateFiniteExact 64 σ := {t with clock := t.clock + 64}
    have same := panPropsEvaluateAddClockEq udivmodTail t out.1 out.2 64 ⟨rfl, by rw [returned]; simp⟩
    have high := evaluate_udivmodTail_enough lifted a b ha hb nz (by simp [lifted])
    have run : (evaluateHOLFiniteState lifted udivmodTail).1 = some (.returned value) := by
      change (evaluateHOLFiniteState {t with clock := t.clock + 64} udivmodTail).1 = _
      rw [same]; exact returned
    exact high.2.2.2 value run
end InitECandidate.Runtime
#print axioms InitECandidate.Runtime.evaluate_udivmodTail
