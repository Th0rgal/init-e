import InitECandidate.Runtime.WordIselCost
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend

/-! The exact selected-code cost of a Word expression: `iselT c` follows
`instSelectExp c` clause by clause, with its constant-offset loads, immediate
operands, `CurrHeap` operands and constant shifts. -/

/-- Selected-code cost of an expression under configuration `c`. -/
def iselT (c : Compiler.Encoders.Asm.AsmConfigExact 64) : WordLangExpHOL (BitVec 64) → Nat
  | .load (.op .add [exp', .const w]) =>
      if WordInst.addrOffsetOk c w then iselT c exp' + 24 else iselT c (.op .add [exp', .const w]) + 24
  | .load exp => iselT c exp + 24
  | .const _ | .var _ | .lookup _ => 24
  | .op op [e1, .const w] =>
      if WordInst.isLookupCurrHeap e1 ∧ op ≠ .sub then 48
      else if c.validImm (.inl op) w then iselT c e1 + 24
      else if op = .add ∧ c.validImm (.inl .sub) (-w) then iselT c e1 + 24
      else iselT c e1 + 48
  | .op op [e1, e2] =>
      if WordInst.isLookupCurrHeap e2 then iselT c e1 + 24
      else if WordInst.isLookupCurrHeap e1 ∧ op ≠ .sub then iselT c e2 + 24
      else iselT c e1 + iselT c e2 + 24
  | .shift _ exp (.const shiftLen) => if shiftLen.toNat < 64 then iselT c exp + 24 else 24
  | .shift _ exp e1 => iselT c exp + iselT c e1 + 28
  | _ => 0
termination_by e => sizeOf e

attribute [local simp] lineBound isLeafProg preAllocLeafBudget rawMovePrice
  WordToStack.refinedWordStackLeafBudget WordToStack.refinedNativeInstructionPrice
  Compiler.Encoders.Asm.HolInst.ofWordLangInst Compiler.Encoders.Asm.HolArith.ofWordLangArith Compiler.Encoders.Asm.HolRegImm.ofWordRegImm

/-- The selected code for an expression costs at most `iselT`. -/
theorem isel_lineBoundT (c : Compiler.Encoders.Asm.AsmConfigExact 64) (tar temp : Nat) :
    ∀ e : WordLangExpHOL (BitVec 64),
      ∃ k, lineBound preAllocLeafBudget (WordInst.instSelectExp c tar temp e) = some k ∧ k ≤ iselT c e
  | .const w => ⟨24, isel_const c tar temp w, by rw [iselT]⟩
  | .var v => ⟨24, isel_var c tar temp v, by rw [iselT]⟩
  | .lookup st => ⟨24, isel_lookup c tar temp st, by rw [iselT]⟩
  | .load exp => by
    rw [WordInst.instSelectExp.eq_def]
    simp only []
    split
    · rename_i exp' w
      rw [iselT]
      split
      · obtain ⟨k, hk, hle⟩ := isel_lineBoundT c temp temp exp'
        rename_i hok
        exact ⟨k + 24, by simp [hk], by omega⟩
      · obtain ⟨k, hk, hle⟩ := isel_lineBoundT c temp temp (.op .add [exp', .const w])
        rename_i hok
        exact ⟨k + 24, by simp [hk], by omega⟩
    · rename_i hnot
      obtain ⟨k, hk, hle⟩ := isel_lineBoundT c temp temp exp
      refine ⟨k + 24, by simp [hk], ?_⟩
      rw [iselT]
      · omega
      · exact hnot
  | .op op [e1, e2] => by
    rw [WordInst.instSelectExp.eq_def]
    simp only []
    obtain ⟨k1, hk1, hle1⟩ := isel_lineBoundT c temp temp e1
    obtain ⟨k2, hk2, hle2⟩ := isel_lineBoundT c temp temp e2
    split
    · rename_i h2
      have hnc : ∀ w, e2 = .const w → False := by
        intro w hw; subst hw; simp [WordInst.isLookupCurrHeap] at h2
      refine ⟨k1 + 24, by simp [hk1], ?_⟩
      rw [iselT]
      · simp [h2]; omega
      · exact hnc
    · rename_i h2
      split
      · rename_i h1
        by_cases hc : ∃ w, e2 = .const w
        · obtain ⟨w, rfl⟩ := hc
          refine ⟨k2 + 24, by simp [hk2], ?_⟩
          have : k2 ≤ 24 := by rw [iselT] at hle2; exact hle2
          rw [iselT]; simp [h1]; omega
        · refine ⟨k2 + 24, by simp [hk2], ?_⟩
          rw [iselT]
          · simp [h2, h1]; omega
          · intro w hw; exact hc ⟨w, hw⟩
      · rename_i h1
        split
        · rename_i w
          rw [iselT]
          split
          · rename_i hv
            refine ⟨k1 + 24, by simp [hk1], ?_⟩
            simp [h1]; omega
          · rename_i hv
            split
            · rename_i hs
              refine ⟨k1 + 24, by simp [hk1], ?_⟩
              simp [hv, hs]; omega
            · rename_i hs
              refine ⟨k1 + 48, by simp [hk1], ?_⟩
              simp [hv, hs]; omega
        · rename_i hnc
          obtain ⟨k3, hk3, hle3⟩ := isel_lineBoundT c (temp + 1) (temp + 1) e2
          refine ⟨k1 + (k3 + 24), by simp [hk1, hk3], ?_⟩
          rw [iselT]
          · simp [h2, h1]; omega
          · exact hnc
  | .op op [] => ⟨0, by rw [WordInst.instSelectExp.eq_def]; simp, by rw [iselT] <;> simp⟩
  | .op op [a] => ⟨0, by rw [WordInst.instSelectExp.eq_def]; simp, by rw [iselT] <;> simp⟩
  | .op op (a :: b :: d :: rest) => ⟨0, by rw [WordInst.instSelectExp.eq_def]; simp, by rw [iselT] <;> simp⟩
  | .shift sh e e1 => by
    rw [WordInst.instSelectExp.eq_def]
    simp only []
    obtain ⟨k, hk, hle⟩ := isel_lineBoundT c temp temp e
    split
    · rename_i shiftLen
      rw [iselT]
      split
      · rename_i hn
        split
        · exact ⟨k + 24, by simp [hk], by omega⟩
        · exact ⟨k + 24, by simp [hk], by omega⟩
      · rename_i hn
        exact ⟨24, by simp, by simp⟩
    · rename_i hnc
      obtain ⟨k1, hk1, hle1⟩ := isel_lineBoundT c (temp + 1) (temp + 1) e1
      refine ⟨k + (k1 + 28), by simp [hk, hk1], ?_⟩
      rw [iselT]
      · omega
      · exact hnc
termination_by e => sizeOf e

/-- Exact selected cost of a statement's expression after `pull_exp` and
`flatten_exp`. -/
def selT (c : Compiler.Encoders.Asm.AsmConfigExact 64) (e : WordLangExpHOL (BitVec 64)) : Nat :=
  iselT c (WordInst.flattenExp (WordInst.ExecutablePullExp.pullExpExecutable e))

theorem isel_assign_lineBoundT (c : Compiler.Encoders.Asm.AsmConfigExact 64) (temp v : Nat)
    (e : WordLangExpHOL (BitVec 64)) :
    ∃ k, lineBound preAllocLeafBudget (WordInst.instSelectExecutable c temp (.assign v e)) = some k ∧
      k ≤ selT c e := by
  simp only [WordInst.instSelectExecutable, selT]
  exact isel_lineBoundT c v temp _

#print axioms isel_lineBoundT
#print axioms isel_assign_lineBoundT
end InitECandidate.Runtime.FineCost
