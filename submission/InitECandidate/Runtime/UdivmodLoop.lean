import InitECandidate.Runtime.UdivmodStep
import InitECandidate.Runtime.RankedLoopExitsInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Loop states differ from a base state only in locals and clock; the
division invariant holds for the current q, r and i. -/
def UdivLoopInv {σ : Type} (base : PanSemStateFiniteExact 64 σ) (a b : BitVec 64)
    (s : PanSemStateFiniteExact 64 σ) : Prop :=
  ∃ q r i : BitVec 64, ∃ L, s = {base with locals := L, clock := s.clock} ∧
    L.lookup (ofString "a") = some (.val (.word a)) ∧ L.lookup (ofString "b") = some (.val (.word b)) ∧
    L.lookup (ofString "q") = some (.val (.word q)) ∧ L.lookup (ofString "r") = some (.val (.word r)) ∧
    L.lookup (ofString "i") = some (.val (.word i)) ∧ i.toNat ≤ 64 ∧ UdivInv a b q r i.toNat

def udivLoopRank {σ : Type} (s : PanSemStateFiniteExact 64 σ) : Nat :=
  match s.locals.lookup (ofString "i") with
  | some (.val (.word i)) => i.toNat
  | _ => 0

theorem udiv_names : ofString "i" ≠ ofString "a" ∧ ofString "i" ≠ ofString "b" ∧ ofString "i" ≠ ofString "q" ∧
    ofString "i" ≠ ofString "r" ∧ ofString "r" ≠ ofString "a" ∧ ofString "r" ≠ ofString "b" ∧
    ofString "r" ≠ ofString "q" ∧ ofString "q" ≠ ofString "a" ∧ ofString "q" ≠ ofString "b" := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> decide_cbv

theorem udivmodLoop_step {σ : Type} (base : PanSemStateFiniteExact 64 σ) (a b : BitVec 64)
    (s : PanSemStateFiniteExact 64 σ) (inv : UdivLoopInv base a b s) (positive : 0 < udivLoopRank s) :
    evaluateHOLFiniteState s udivmodStep = (none, (evaluateHOLFiniteState s udivmodStep).2) ∧
      UdivLoopInv base a b (evaluateHOLFiniteState s udivmodStep).2 ∧
      udivLoopRank (evaluateHOLFiniteState s udivmodStep).2 < udivLoopRank s ∧
      (evaluateHOLFiniteState s udivmodStep).2.clock = s.clock := by
  obtain ⟨q, r, i, L, shape, ha, hb, hq, hr, hi, bound, arith⟩ := inv
  obtain ⟨n1,n2,n3,n4,n5,n6,n7,n8,n9⟩ := udiv_names
  have hs : ∀ name, s.locals.lookup name = L.lookup name := by intro name; rw [shape]
  have rank : udivLoopRank s = i.toNat := by simp [udivLoopRank, hs, hi]
  rw [rank] at positive
  have nz : i ≠ 0 := fun e => by subst e; simp at positive
  have run := evaluate_udivmodStep s a b q r i (by rw [hs]; exact ha) (by rw [hs]; exact hb)
    (by rw [hs]; exact hq) (by rw [hs]; exact hr) (by rw [hs]; exact hi) nz bound
  rw [run]
  have predNat : (i - 1).toNat = i.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp
  have arith' : UdivInv a b q r ((i.toNat - 1) + 1) := by
    rw [show i.toNat - 1 + 1 = i.toNat by omega]; exact arith
  have stepArith := udivInv_step a b q r (i.toNat - 1) arith'
  have r1eq : udivmodR1 a r i = udivR1 a r (i.toNat - 1) := by
    unfold udivmodR1 udivR1; rw [predNat]; rfl
  have arithLess : udivmodR1 a r i < b → UdivInv a b q (udivmodR1 a r i) (i - 1).toNat := by
    intro less; rw [predNat, r1eq]; exact stepArith.2 (by rw [← r1eq]; exact less)
  have arithGe : ¬ udivmodR1 a r i < b →
      UdivInv a b (q ||| ((1 : BitVec 64) <<< (i - 1).toNat)) (udivmodR1 a r i - b) (i - 1).toNat := by
    intro less; rw [predNat, r1eq]; exact stepArith.1 (by rw [← r1eq]; exact less)
  refine ⟨rfl, ?_, ?_, ?_⟩
  · unfold udivmodStepState
    by_cases less : udivmodR1 a r i < b
    · simp only [if_pos less]
      refine ⟨q, udivmodR1 a r i, i - 1, (setVarHOLFinite (ofString "r") (.val (.word (udivmodR1 a r i)))
        (setVarHOLFinite (ofString "i") (.val (.word (i - 1))) s)).locals, ?_, ?_, ?_, ?_, ?_, ?_, by omega,
        arithLess less⟩
      · rw [shape]; rfl
      all_goals simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, n1, n2, n3, n5, n6, n7,
        n9, Ne.symm n1, Ne.symm n2, Ne.symm n3, Ne.symm n4, Ne.symm n5, Ne.symm n6, Ne.symm n7, hs, ha, hb, hq]
    · simp only [if_neg less]
      refine ⟨q ||| ((1 : BitVec 64) <<< (i - 1).toNat), udivmodR1 a r i - b, i - 1,
        (setVarHOLFinite (ofString "q") (.val (.word (q ||| ((1 : BitVec 64) <<< (i - 1).toNat))))
          (setVarHOLFinite (ofString "r") (.val (.word (udivmodR1 a r i - b)))
            (setVarHOLFinite (ofString "r") (.val (.word (udivmodR1 a r i)))
              (setVarHOLFinite (ofString "i") (.val (.word (i - 1))) s)))).locals,
        ?_, ?_, ?_, ?_, ?_, ?_, by omega, arithGe less⟩
      · rw [shape]; rfl
      all_goals simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, n1, n2, n3, n4, n5, n6, n7,
        n8, n9, Ne.symm n1, Ne.symm n2, Ne.symm n3, Ne.symm n4, Ne.symm n5, Ne.symm n6, Ne.symm n7, hs, ha, hb, hq]
  · have iPost : (udivmodStepState s a b q r i).locals.lookup (ofString "i") = some (.val (.word (i - 1))) := by
      unfold udivmodStepState
      split <;> simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, n3, n4, Ne.symm n3, Ne.symm n4]
    rw [rank]
    simp only [udivLoopRank, iPost, predNat]
    omega
  · unfold udivmodStepState
    split <;> rfl

#print axioms udivmodLoop_step
end InitECandidate.Runtime
