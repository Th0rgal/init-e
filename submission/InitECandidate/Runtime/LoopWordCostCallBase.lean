import InitECandidate.Runtime.LoopWordCostBase
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact

/-! Word-side unfolding of the compiled calls. -/

section
variable {C F : Type}

theorem call_cost_zero (ret dest args handler) (t : WordSemStateFiniteExact 64 C F) (zero : t.clock = 0) :
    wordExecutionCost loopWordPrice (.call ret dest args handler) t =
      loopWordPrice (.call ret dest args handler) t := by
  cases ret <;> cases handler <;> rw [wordExecutionCost] <;> repeat' split
  all_goals simp_all

theorem tail_call_cost (dest : Option Nat) (args : List Nat) (t : WordSemStateFiniteExact 64 C F)
    {xs args1 prog ss}
    (hargs : getVars args t = some xs) (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest (wordSemAddRetLoc
      (none : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec 64) × Nat × Nat)) xs)
      t.code t.stackSize = some (args1, prog, ss))
    (nz : t.clock ≠ 0) :
    wordExecutionCost loopWordPrice (.call none dest args none) t =
      args.length + wordExecutionCost loopWordPrice prog (callEnv args1 ss (decClock t)) := by
  rw [wordExecutionCost]
  simp only [hargs, hbad, Bool.false_eq_true, ↓reduceIte, hfind, nz, ↓reduceDIte, loopWordPrice]

/-- Words returned by a callee body. -/
def wordRetWords : Option (WordSemResult 64) → Nat
  | some (.result _ values) => values.length
  | _ => 0

/-- A returning call pays its return names only when the body returns. -/
theorem ret_price_le (rets : List Nat) (cutset : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64))
    (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (t : WordSemStateFiniteExact 64 C F) {xs args1 prog ss envs r m}
    (hargs : getVars args t = some xs)
    (hfind : wordSemFindCode dest (wordSemAddRetLoc (some (rets, cutset, retCode, l1, l2)) xs) t.code
      t.stackSize = some (args1, prog, ss))
    (hcut : wordSemCutEnvs cutset t.locals = some envs)
    (run : evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock t))) = (r, m)) :
    loopWordPrice (.call (some (rets, cutset, retCode, l1, l2)) dest args handler) t ≤
      args.length + wordRetWords r := by
  rw [loopWordPrice]
  split
  · rename_i h
    obtain ⟨-, xs', args1', prog', ss', envs', loc, vals, m', h1, h2, h3, h4, h5⟩ := h
    rw [hargs] at h1; cases h1
    rw [hfind] at h2; cases h2
    rw [hcut] at h3; cases h3
    rw [run] at h4; cases h4
    simp [wordRetWords, h5]
  · omega

/-- A returning call costs at most its price, the callee body, and the
continuation selected by the body's result. -/
theorem ret_call_cost_le (rets : List Nat) (cutset : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64))
    (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (t : WordSemStateFiniteExact 64 C F) {xs args1 prog ss envs r m}
    (hargs : getVars args t = some xs) (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest (wordSemAddRetLoc (some (rets, cutset, retCode, l1, l2)) xs) t.code
      t.stackSize = some (args1, prog, ss))
    (hcut : wordSemCutEnvs cutset t.locals = some envs) (nz : t.clock ≠ 0)
    (run : evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock t))) = (r, m)) :
    wordExecutionCost loopWordPrice (.call (some (rets, cutset, retCode, l1, l2)) dest args handler) t ≤
      args.length + wordRetWords r +
        wordExecutionCost loopWordPrice prog (callEnv args1 ss (pushEnv envs handler (decClock t))) +
        (match (generalizing := false) r with
          | some (.result _ returned) =>
              (match popEnv m with
                | some popped => wordExecutionCost loopWordPrice retCode (setVars rets returned popped)
                | none => 0)
          | some (.exception _ value) =>
              (match (generalizing := false) handler with
                | some (reg, handlerCode, _, _) =>
                    wordExecutionCost loopWordPrice handlerCode (setVar reg value m)
                | none => 0)
          | _ => 0) := by
  have hp := ret_price_le rets cutset retCode l1 l2 dest args handler t hargs hfind hcut run
  rw [wordExecutionCost]
  generalize loopWordPrice (.call (some (rets, cutset, retCode, l1, l2)) dest args handler) t = P at hp ⊢
  simp only [hargs, hbad, Bool.false_eq_true, ↓reduceIte, hfind]
  split
  · omega
  · simp only [hcut, nz, ↓reduceDIte]
    split
    next _ returned _ hm =>
      rw [fix_clock_evaluate, run] at hm
      cases hm
      simp only [wordRetWords] at hp ⊢
      split
      · omega
      · cases hp' : popEnv m with
        | none => simp only; omega
        | some popped => simp only; split <;> omega
    next _ value _ hm =>
      rw [fix_clock_evaluate, run] at hm
      cases hm
      simp only [wordRetWords] at hp ⊢
      cases handler with
      | none => simp only; omega
      | some h =>
        obtain ⟨reg, hc, h1, h2⟩ := h
        simp only
        split
        · omega
        · split <;> omega
    next => omega
end

#print axioms call_cost_zero
#print axioms tail_call_cost
#print axioms ret_price_le
#print axioms ret_call_cost_le
end InitECandidate.Runtime.FineCost
