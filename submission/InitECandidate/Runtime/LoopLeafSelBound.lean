import InitECandidate.Runtime.WordIselCost
import InitECandidate.Runtime.LoopWordPLLeafRen
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend

/-! A structural bound on the selected-code cost of an expression statement.
`fW` charges 24 per constant, variable or lookup, 24 per `load`, 28 per
`shift`, and an `n`-ary operator its arguments plus 24 per extra argument (an
empty operator is a constant). Instruction selection's preprocessing
(`pullExpExecutable`, then `flattenExp`) never exceeds it. -/

mutual
/-- Structural selector bound of a Word expression. -/
def fW : WordLangExpHOL (BitVec 64) → Nat
  | .const _ | .var _ | .lookup _ => 24
  | .load e => fW e + 24
  | .op _ args => fWs args + 24 * (args.length - 1) + 24 * (1 - args.length)
  | .shift _ e e1 => fW e + fW e1 + 28

/-- Sum of `fW` over a list. -/
def fWs : List (WordLangExpHOL (BitVec 64)) → Nat
  | [] => 0
  | a :: as => fW a + fWs as
end

theorem fWs_append : ∀ (l r : List (WordLangExpHOL (BitVec 64))), fWs (l ++ r) = fWs l + fWs r
  | [], r => by simp [fWs]
  | a :: l, r => by simp only [List.cons_append, fWs, fWs_append l r]; omega

theorem fW_pos : ∀ e : WordLangExpHOL (BitVec 64), 24 ≤ fW e
  | .const _ | .var _ | .lookup _ => by simp [fW]
  | .load e => by simp only [fW]; omega
  | .op _ args => by
    simp only [fW]
    rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp
    · have := fW_pos a; simp only [fWs, List.length_cons, List.length_nil]; omega
    · have := fW_pos a; simp only [fWs, List.length_cons]; omega
  | .shift _ e e1 => by simp only [fW]; omega

theorem iselCost_flatten (e : WordLangExpHOL (BitVec 64)) : iselCost (WordInst.flattenExp e) ≤ fW e := by
  refine (measure (sizeOf : WordLangExpHOL (BitVec 64) → Nat)).wf.induction (C := fun e =>
    iselCost (WordInst.flattenExp e) ≤ fW e) e ?_
  intro e ih
  cases e with
  | const w => rw [WordInst.flattenExp.eq_def]; simp [fW]
  | var v => rw [WordInst.flattenExp.eq_def]; simp [fW]
  | lookup st => rw [WordInst.flattenExp.eq_def]; simp [fW]
  | load a =>
    have := ih a (by show sizeOf a < _; simp)
    rw [WordInst.flattenExp]; simp only [iselCost_load, fW]; omega
  | shift sh a b =>
    have ha := ih a (by show sizeOf a < _; simp; omega)
    have hb := ih b (by show sizeOf b < _; simp)
    rw [WordInst.flattenExp]; simp only [iselCost_shift, fW]; omega
  | op o args =>
    by_cases hs : o = .sub
    · subst hs
      rw [WordInst.flattenExp]
      rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
      · simp [iselCost]
      · simp [iselCost]
      · have ha := ih a (by show sizeOf a < _; simp; omega)
        have hb := ih b (by show sizeOf b < _; simp; omega)
        simp only [List.attach_cons, List.attach_nil, List.map_cons, List.map_nil, List.map_attach_eq_pmap]
        simp only [List.pmap, iselCost_op2, fW, fWs, List.length_cons, List.length_nil]; omega
      · simp [iselCost]
    · rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · rw [WordInst.flattenExp.eq_def]; simp only
        cases o <;> first | exact absurd rfl hs | simp [WordInst.opConsts, fW]
      · have ha := ih a (by show sizeOf a < _; simp; omega)
        rw [WordInst.flattenExp.eq_def]; simp only
        cases o <;> first | exact absurd rfl hs | (simp only [fW, fWs, List.length_cons, List.length_nil]; omega)
      · have ha := ih a (by show sizeOf a < _; simp; omega)
        have hrest := ih (.op o (b :: rest)) (by show sizeOf _ < _; simp)
        rw [WordInst.flattenExp.eq_def]; simp only
        cases o <;> first
          | exact absurd rfl hs
          | (simp only [iselCost_op2, fW, fWs, List.length_cons] at hrest ⊢; omega)

#print axioms iselCost_flatten

/-- Slot potential of an argument list: each argument plus one operator slot. -/
def pot (L : List (WordLangExpHOL (BitVec 64))) : Nat := fWs L + 24 * L.length

theorem pot_cons (a : WordLangExpHOL (BitVec 64)) (L : List (WordLangExpHOL (BitVec 64))) :
    pot (a :: L) = fW a + 24 + pot L := by simp only [pot, fWs, List.length_cons]; omega

theorem pot_append (l r : List (WordLangExpHOL (BitVec 64))) : pot (l ++ r) = pot l + pot r := by
  simp only [pot, fWs_append, List.length_append]; omega

theorem fW_op (o : BinOp) (L : List (WordLangExpHOL (BitVec 64))) :
    fW (.op o L) + 24 = (if L = [] then 48 else pot L) := by
  rcases L with _ | ⟨a, L⟩
  · simp [fW, fWs]
  · simp only [fW, pot, fWs, List.length_cons, reduceCtorEq, if_false]; omega

theorem pot_ge (L : List (WordLangExpHOL (BitVec 64))) : 48 * L.length ≤ pot L := by
  induction L with
  | nil => simp [pot]
  | cons a L ih => have := fW_pos a; rw [pot_cons]; simp only [List.length_cons]; omega

theorem pullOps_pot (o : BinOp) : ∀ (xs acc : List (WordLangExpHOL (BitVec 64))),
    pot (WordInst.pullOps o xs acc) ≤ pot xs + pot acc
  | [], acc => by simp [WordInst.pullOps, pot, fWs]
  | x :: xs, acc => by
    by_cases hx : ∃ o' ls, x = .op o' ls
    · obtain ⟨o', ls, rfl⟩ := hx
      simp only [WordInst.pullOps]
      split
      · have := pullOps_pot o xs (ls ++ acc)
        have h := fW_op o' ls
        rw [pot_append] at this; rw [pot_cons]
        rcases ls with _ | ⟨l0, ls⟩
        · simp only [pot, fWs, List.length_nil, if_true] at this h ⊢; omega
        · simp only [reduceCtorEq, if_false] at h; omega
      · have := pullOps_pot o xs (.op o' ls :: acc)
        rw [pot_cons] at this; rw [pot_cons]; omega
    · have hp : WordInst.pullOps o (x :: xs) acc = WordInst.pullOps o xs (x :: acc) := by
        cases x <;> first | (exfalso; exact hx ⟨_, _, rfl⟩) | simp [WordInst.pullOps]
      rw [hp]
      have := pullOps_pot o xs (x :: acc)
      rw [pot_cons] at this; rw [pot_cons]; omega

theorem holPart_pot (Pr : WordLangExpHOL (BitVec 64) → Bool) : ∀ (l a b : List (WordLangExpHOL (BitVec 64))),
    pot (holPart Pr l a b).1 + pot (holPart Pr l a b).2 = pot l + pot a + pot b
  | [], a, b => by simp [holPart, pot, fWs]
  | h :: rst, a, b => by
    simp only [holPart]
    split
    · have := holPart_pot Pr rst (h :: a) b; rw [pot_cons] at this; rw [pot_cons]; omega
    · have := holPart_pot Pr rst a (h :: b); rw [pot_cons] at this; rw [pot_cons]; omega

#print axioms holPart_pot

theorem fW_op_max (o : BinOp) (L : List (WordLangExpHOL (BitVec 64))) : fW (.op o L) + 24 = max 48 (pot L) := by
  have h := fW_op o L
  rcases L with _ | ⟨a, L⟩
  · simp only [if_true, pot, fWs, List.length_nil] at h ⊢; omega
  · have := pot_ge (a :: L)
    simp only [reduceCtorEq, if_false, List.length_cons] at h this; omega

theorem pot_nil : pot ([] : List (WordLangExpHOL (BitVec 64))) = 0 := by simp [pot, fWs]

theorem optimizeNonSub_fW (o : BinOp) (h : o ≠ .sub) (L : List (WordLangExpHOL (BitVec 64))) :
    fW (WordInst.ExecutablePullExp.optimizeNonSub o h L) ≤ fW (.op o L) := by
  unfold WordInst.ExecutablePullExp.optimizeNonSub holPartition
  have hp := holPart_pot (fun e => WordInst.isConst e) L [] []
  generalize holPart (fun e => WordInst.isConst e) L [] [] = part at hp ⊢
  rcases part with ⟨cs, ns⟩
  rw [pot_nil] at hp
  simp only [Nat.add_zero] at hp
  have hL := fW_op_max o L
  rcases cs with _ | ⟨c0, cs⟩
  · simp only
    have := fW_op_max o ns
    rw [pot_nil] at hp; omega
  · simp only
    have hcs := pot_ge cs
    have hc0 := fW_pos c0
    rw [pot_cons] at hp
    have hconst : ∀ w : BitVec 64, fW (.const w) ≤ fW (.op o L) := fun w =>
      Nat.le_trans (Nat.le_of_eq (by simp [fW])) (fW_pos _)
    unfold WordInst.reduceConst
    split_ifs
    · split
      · exact hconst _
      · rename_i x
        rw [pot_cons, pot_nil] at hp; omega
      · have := fW_op_max o ns; omega
    · exact hconst _
    · generalize WordInst.ExecutablePullExp.nonSubWordOp o h _ = w at *
      have := fW_op_max o (.const w :: ns)
      have hc : fW (.const w) = 24 := by simp [fW]
      rw [pot_cons, hc] at this; omega
    · generalize WordInst.ExecutablePullExp.nonSubWordOp o h _ = w at *
      have := fW_op_max o (.const w :: ns)
      have hc : fW (.const w) = 24 := by simp [fW]
      rw [pot_cons, hc] at this; omega

theorem convertSub_fW (L : List (WordLangExpHOL (BitVec 64))) :
    fW (WordInst.convertSub L) ≤ fW (.op .sub L) := by
  rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp [WordInst.convertSub]
  · simp [WordInst.convertSub]
  · cases a <;> cases b <;> simp [WordInst.convertSub, fW, fWs] <;> omega
  · simp [WordInst.convertSub]

#print axioms optimizeNonSub_fW

theorem pot_map_le (f : WordLangExpHOL (BitVec 64) → WordLangExpHOL (BitVec 64)) :
    ∀ (L : List (WordLangExpHOL (BitVec 64))), (∀ a ∈ L, fW (f a) ≤ fW a) → pot (L.map f) ≤ pot L
  | [], _ => by simp [pot_nil]
  | a :: L, h => by
    simp only [List.map_cons, pot_cons]
    have := pot_map_le f L (fun b hb => h b (by simp [hb]))
    have := h a (by simp); omega

theorem fW_pull (e : WordLangExpHOL (BitVec 64)) :
    fW (WordInst.ExecutablePullExp.pullExpExecutable e) ≤ fW e := by
  refine (measure (sizeOf : WordLangExpHOL (BitVec 64) → Nat)).wf.induction (C := fun e =>
    fW (WordInst.ExecutablePullExp.pullExpExecutable e) ≤ fW e) e ?_
  intro e ih
  cases e with
  | op o ls =>
    have ihl : ∀ a ∈ ls, fW (WordInst.ExecutablePullExp.pullExpExecutable a) ≤ fW a := fun a ha =>
      ih a (by have := List.sizeOf_lt_of_mem ha; show sizeOf a < _; simp; omega)
    have hpot := pot_map_le _ ls ihl
    rw [WordInst.ExecutablePullExp.pullExpExecutable]
    by_cases hs : o = .sub
    · subst hs
      simp only [dif_pos, map_attach_val]
      have h1 := convertSub_fW (ls.map WordInst.ExecutablePullExp.pullExpExecutable)
      have h2 := fW_op_max .sub (ls.map WordInst.ExecutablePullExp.pullExpExecutable)
      have h3 := fW_op_max .sub ls
      omega
    · simp only [hs, dif_neg, not_false_eq_true]
      rcases ls with _ | ⟨x, _ | ⟨y, rest⟩⟩
      · cases o <;> first | exact absurd rfl hs | simp [WordInst.opConsts, fW, fWs]
      · have := ihl x (by simp); simp only [fW, fWs, List.length_cons, List.length_nil]; omega
      · simp only [map_attach_val]
        have h1 := optimizeNonSub_fW o hs
          (WordInst.pullOps o ((x :: y :: rest).map WordInst.ExecutablePullExp.pullExpExecutable) [])
        have h2 := pullOps_pot o ((x :: y :: rest).map WordInst.ExecutablePullExp.pullExpExecutable) []
        have h3 := fW_op_max o (WordInst.pullOps o ((x :: y :: rest).map WordInst.ExecutablePullExp.pullExpExecutable) [])
        have h4 := fW_op_max o (x :: y :: rest)
        rw [pot_nil] at h2
        omega
  | load a =>
    have := ih a (by show sizeOf a < _; simp)
    rw [WordInst.ExecutablePullExp.pullExpExecutable]; simp only [fW]; omega
  | shift sh a b =>
    have ha := ih a (by show sizeOf a < _; simp; omega)
    have hb := ih b (by show sizeOf b < _; simp)
    rw [WordInst.ExecutablePullExp.pullExpExecutable]; simp only [fW]; omega
  | const w => rw [WordInst.ExecutablePullExp.pullExpExecutable.eq_def]
  | var v => rw [WordInst.ExecutablePullExp.pullExpExecutable.eq_def]
  | lookup st => rw [WordInst.ExecutablePullExp.pullExpExecutable.eq_def]

/-- The selected code of an assignment costs at most `fW` of its expression. -/
theorem iselX_assign_le (c : Compiler.Encoders.Asm.AsmConfigExact 64) (v : Nat) (e : WordLangExpHOL (BitVec 64)) :
    iselX c (.assign v e) ≤ fW e := by
  obtain ⟨k, hk, hle⟩ := isel_assign_lineBound c 0 v e
  have h1 := iselCost_flatten (WordInst.ExecutablePullExp.pullExpExecutable e)
  have h2 := fW_pull e
  simp only [iselX, hk, Option.getD_some]
  simp only [selExpCost] at hle
  omega

#print axioms iselX_assign_le
end InitECandidate.Runtime.FineCost
