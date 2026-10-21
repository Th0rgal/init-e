import InitECandidate.Runtime.LoopWordPBase
import InitECandidate.Runtime.LoopWordCostCallBase
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact

/-! Price-generic Word call unfoldings and the dominated call price. -/

section
variable {C F : Type}

theorem call_cost_zeroG (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (ret dest args handler) (t : WordSemStateFiniteExact 64 C F) (zero : t.clock = 0) :
    wordExecutionCost price (.call ret dest args handler) t = price (.call ret dest args handler) t := by
  cases ret <;> cases handler <;> rw [wordExecutionCost] <;> repeat' split
  all_goals simp_all

theorem tail_call_costG (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (dest : Option Nat) (args : List Nat) (t : WordSemStateFiniteExact 64 C F) {xs args1 prog ss}
    (hargs : getVars args t = some xs) (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest (wordSemAddRetLoc
      (none : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec 64) × Nat × Nat)) xs)
      t.code t.stackSize = some (args1, prog, ss))
    (nz : t.clock ≠ 0) :
    wordExecutionCost price (.call none dest args none) t =
      price (.call none dest args none) t + wordExecutionCost price prog (callEnv args1 ss (decClock t)) := by
  rw [wordExecutionCost]
  simp only [hargs, hbad, Bool.false_eq_true, ↓reduceIte, hfind, nz, ↓reduceDIte]

theorem ret_call_cost_leG (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat) (rets : List Nat) (cutset : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64))
    (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (t : WordSemStateFiniteExact 64 C F) {xs args1 prog ss envs r m}
    (hargs : getVars args t = some xs) (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest (wordSemAddRetLoc (some (rets, cutset, retCode, l1, l2)) xs) t.code
      t.stackSize = some (args1, prog, ss))
    (hcut : wordSemCutEnvs cutset t.locals = some envs) (nz : t.clock ≠ 0)
    (run : evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock t))) = (r, m)) :
    wordExecutionCost price (.call (some (rets, cutset, retCode, l1, l2)) dest args handler) t ≤
      price (.call (some (rets, cutset, retCode, l1, l2)) dest args handler) t +
        wordExecutionCost price prog (callEnv args1 ss (pushEnv envs handler (decClock t))) +
        (match (generalizing := false) r with
          | some (.result _ returned) =>
              (match popEnv m with
                | some popped => wordExecutionCost price retCode (setVars rets returned popped)
                | none => 0)
          | some (.exception _ value) =>
              (match (generalizing := false) handler with
                | some (reg, handlerCode, _, _) =>
                    wordExecutionCost price handlerCode (setVar reg value m)
                | none => 0)
          | _ => 0) := by
  rw [wordExecutionCost]
  generalize price (.call (some (rets, cutset, retCode, l1, l2)) dest args handler) t = P
  simp only [hargs, hbad, Bool.false_eq_true, ↓reduceIte, hfind]
  split
  · omega
  · simp only [hcut, nz, ↓reduceDIte]
    split
    next _ returned _ hm =>
      rw [fix_clock_evaluate, run] at hm
      cases hm
      split
      · omega
      · cases hp' : popEnv m with
        | none => simp only; omega
        | some popped => simp only; split <;> omega
    next _ value _ hm =>
      rw [fix_clock_evaluate, run] at hm
      cases hm
      cases handler with
      | none => simp only; omega
      | some h =>
        obtain ⟨reg, hc, h1, h2⟩ := h
        simp only
        split
        · omega
        · split <;> omega
    next => omega
open Classical in
/-- Returned names are paid only when the body returns that arity. -/
theorem ret_paid_le (R : Nat) (rets : List Nat) (cutset : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64))
    (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (t : WordSemStateFiniteExact 64 C F) {xs args1 prog ss envs r m}
    (hargs : getVars args t = some xs)
    (hfind : wordSemFindCode dest (wordSemAddRetLoc (some (rets, cutset, retCode, l1, l2)) xs) t.code
      t.stackSize = some (args1, prog, ss))
    (hcut : wordSemCutEnvs cutset t.locals = some envs)
    (run : evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock t))) = (r, m)) :
    (if wordCallReturned (.call (some (rets, cutset, retCode, l1, l2)) dest args handler) t
      then R * rets.length else 0) ≤ R * wordRetWords r := by
  split
  · rename_i h
    obtain ⟨-, xs', args1', prog', ss', envs', loc, vals, m', h1, h2, h3, h4, h5⟩ := h
    rw [hargs] at h1; cases h1
    rw [hfind] at h2; cases h2
    rw [hcut] at h3; cases h3
    rw [run] at h4; cases h4
    simp [wordRetWords, h5]
  · omega

theorem ret_unpaid_zero (R : Nat) (rets : List Nat) (cutset : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64))
    (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (t : WordSemStateFiniteExact 64 C F) (zero : t.clock = 0) :
    (open Classical in if wordCallReturned (.call (some (rets, cutset, retCode, l1, l2)) dest args handler) t
      then R * rets.length else 0) = 0 := by
  classical
  rw [if_neg (fun h => h.1 zero)]
end

#print axioms ret_call_cost_leG
#print axioms ret_paid_le
end InitECandidate.Runtime.FineCost
