import InitECandidate.Runtime.WordCompileExpCost
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordInst
open Flapjack.Compiler.Backend.WordInst.ExecutablePullExp

/-- Structural (fuel) copy of `pullExpExecutable`, for kernel evaluation. -/
def pullF : Nat → WordLangExpHOL (BitVec 64) → WordLangExpHOL (BitVec 64)
  | 0, e => e
  | n + 1, .op op ls =>
      if h : op = .sub then convertSub (ls.map (pullF n))
      else
        match ls with
        | [] => opConsts op
        | [x] => pullF n x
        | x :: y :: rest => optimizeNonSub op h (pullOps op ((x :: y :: rest).map (pullF n)) [])
  | n + 1, .load e => .load (pullF n e)
  | n + 1, .shift sh a b => .shift sh (pullF n a) (pullF n b)
  | _ + 1, e => e

theorem pullF_eq : ∀ (n : Nat) (e : WordLangExpHOL (BitVec 64)), sizeOf e < n → pullF n e = pullExpExecutable e
  | 0, e, h => absurd h (Nat.not_lt_zero _)
  | n + 1, e, h => by
    cases e with
    | op op ls =>
      have hm : ls.map (pullF n) = ls.map pullExpExecutable := by
        apply List.map_congr_left
        intro x hx
        apply pullF_eq n x
        have := List.sizeOf_lt_of_mem hx
        simp at h; omega
      by_cases hs : op = .sub
      · subst hs
        simp only [pullF, dif_pos, pullExpExecutable, List.map_attach_eq_pmap, List.pmap_eq_map, hm]
      · rcases ls with _ | ⟨a, _ | ⟨b, rest⟩⟩
        · simp only [pullF, dif_neg hs]; rw [pullExpExecutable]; simp [hs]
        · simp only [pullF, dif_neg hs]
          rw [pullExpExecutable]
          simp only [dif_neg hs]
          exact pullF_eq n a (by simp at h; omega)
        · simp only [pullF, dif_neg hs]
          rw [pullExpExecutable]
          simp only [dif_neg hs, List.map_attach_eq_pmap, List.pmap_eq_map]
          rw [hm]
    | load e =>
      simp only [pullF]; rw [pullExpExecutable, pullF_eq n e (by simp at h; omega)]
    | shift sh a b =>
      simp only [pullF]
      rw [pullExpExecutable, pullF_eq n a (by simp at h; omega), pullF_eq n b (by simp at h; omega)]
    | const _ | var _ | lookup _ => simp [pullF, pullExpExecutable]

/-- Structural (fuel) copy of `flattenExp`. -/
def flattenF : Nat → WordLangExpHOL (BitVec 64) → WordLangExpHOL (BitVec 64)
  | 0, e => e
  | n + 1, .op op ls =>
      if op = .sub then .op .sub (ls.map (flattenF n))
      else
        match ls with
        | [] => opConsts op
        | [x] => flattenF n x
        | x :: xs => .op op [flattenF n (.op op xs), flattenF n x]
  | n + 1, .load e => .load (flattenF n e)
  | n + 1, .shift sh a b => .shift sh (flattenF n a) (flattenF n b)
  | _ + 1, e => e

theorem flatten_nil (op : BinOp) (hs : op ≠ .sub) :
    flattenExp (.op op [] : WordLangExpHOL (BitVec 64)) = opConsts op := by
  cases op <;> first | exact absurd rfl hs | (rw [flattenExp] <;> intros <;> simp_all)

theorem flatten_one (op : BinOp) (hs : op ≠ .sub) (a : WordLangExpHOL (BitVec 64)) :
    flattenExp (.op op [a]) = flattenExp a := by
  cases op <;> first | exact absurd rfl hs | (nth_rw 1 [flattenExp] <;> intros <;> simp_all)

theorem flatten_cons2 (op : BinOp) (hs : op ≠ .sub) (a b : WordLangExpHOL (BitVec 64)) (rest) :
    flattenExp (.op op (a :: b :: rest)) = .op op [flattenExp (.op op (b :: rest)), flattenExp a] := by
  cases op <;> first | exact absurd rfl hs | (nth_rw 1 [flattenExp] <;> intros <;> simp_all)

theorem flattenF_eq : ∀ (n : Nat) (e : WordLangExpHOL (BitVec 64)), sizeOf e < n → flattenF n e = flattenExp e
  | 0, e, h => absurd h (Nat.not_lt_zero _)
  | n + 1, e, h => by
    cases e with
    | op op ls =>
      by_cases hs : op = .sub
      · subst hs
        have hm : ls.map (flattenF n) = ls.map flattenExp := by
          apply List.map_congr_left
          intro x hx
          apply flattenF_eq n x
          have := List.sizeOf_lt_of_mem hx
          simp at h; omega
        simp only [flattenF, if_pos, hm]
        rw [flattenExp]
        simp [List.map_attach_eq_pmap, List.pmap_eq_map]
      · rcases ls with _ | ⟨a, _ | ⟨b, rest⟩⟩
        · simp only [flattenF, if_neg hs]; rw [flatten_nil op hs]
        · simp only [flattenF, if_neg hs]
          rw [flattenF_eq n a (by simp at h; omega), flatten_one op hs]
        · simp only [flattenF, if_neg hs]
          rw [flattenF_eq n a (by simp at h; omega), flattenF_eq n (.op op (b :: rest)) (by simp at h ⊢; omega),
            flatten_cons2 op hs]
    | load e =>
      simp only [flattenF]; rw [flattenExp, flattenF_eq n e (by simp at h; omega)]
    | shift sh a b =>
      simp only [flattenF]
      rw [flattenExp, flattenF_eq n a (by simp at h; omega), flattenF_eq n b (by simp at h; omega)]
    | const _ | var _ | lookup _ => simp [flattenF, flattenExp]

/-- Structural (fuel) copy of `constFpExp`. -/
def cfpF : Nat → WordLangExpHOL (BitVec 64) → Spt (BitVec 64) → WordLangExpHOL (BitVec 64)
  | 0, e, _ => e
  | _ + 1, .var v, cs =>
      match sptLookup v cs with
      | some x => .const x
      | none => .var v
  | n + 1, .op op args, cs =>
      let a := args.map (fun e => cfpF n e cs)
      match WordSimp.stripConst a with
      | some ws =>
          match wordOpHOL op ws with
          | some w => .const w
          | none => .op op (ws.map .const)
      | none => .op op a
  | n + 1, .shift sh e e1, cs =>
      let a := cfpF n e cs
      let b := cfpF n e1 cs
      match a, b with
      | .const c, .const c1 =>
          match wordShiftHOL sh c c1.toNat with
          | some w => .const w
          | none => .shift sh (.const c) (.const c1)
      | _, _ => .shift sh a b
  | _ + 1, e, _ => e

theorem cfpF_eq : ∀ (n : Nat) (e : WordLangExpHOL (BitVec 64)) (cs : Spt (BitVec 64)), sizeOf e < n →
    cfpF n e cs = WordSimp.constFpExp e cs
  | 0, e, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, e, cs, h => by
    cases e with
    | var v => simp only [cfpF]; rw [WordSimp.constFpExp]; rcases sptLookup v cs <;> rfl
    | op op args =>
      have hm : args.map (fun e => cfpF n e cs) = args.map (fun e => WordSimp.constFpExp e cs) := by
        apply List.map_congr_left
        intro x hx
        apply cfpF_eq n x cs
        have := List.sizeOf_lt_of_mem hx
        simp at h; omega
      simp only [cfpF, hm]
      rw [WordSimp.constFpExp]
      simp only [List.map_attach_eq_pmap, List.pmap_eq_map]
      rcases WordSimp.stripConst (List.map (fun e => WordSimp.constFpExp e cs) args) with _ | ws
      · rfl
      · simp only; rcases wordOpHOL op ws <;> rfl
    | shift sh a b =>
      simp only [cfpF]
      rw [cfpF_eq n a cs (by simp at h; omega), cfpF_eq n b cs (by simp at h; omega), WordSimp.constFpExp]
      rcases WordSimp.constFpExp a cs with _ | _ | _ | _ | _ | _ <;> rcases WordSimp.constFpExp b cs with _ | _ | _ | _ | _ | _
      all_goals try rfl
      rename_i x y; cases hw : wordShiftHOL sh x y.toNat <;> simp [hw]
    | const _ | lookup _ | load _ => simp only [cfpF]; rw [WordSimp.constFpExp] <;> intros <;> simp_all

/-- Structural (fuel) copy of `instSelectExp`. -/
def iselF (c : Compiler.Encoders.Asm.AsmConfigExact 64) :
    Nat → Nat → Nat → WordLangExpHOL (BitVec 64) → WordLangProgHOL (BitVec 64)
  | 0, _, _, _ => .skip
  | n + 1, tar, temp, .load exp =>
      match exp with
      | .op .add [exp', .const w] =>
          if addrOffsetOk c w then .seq (iselF c n temp temp exp') (.inst (.mem .load tar (.addr temp w)))
          else .seq (iselF c n temp temp exp) (.inst (.mem .load tar (.addr temp 0)))
      | _ => .seq (iselF c n temp temp exp) (.inst (.mem .load tar (.addr temp 0)))
  | _ + 1, tar, _, .const w => .inst (.const tar w)
  | _ + 1, tar, _, .var v => .move 0 [(tar, v)]
  | _ + 1, tar, _, .lookup storeName => .get tar storeName
  | n + 1, tar, temp, .op op [e1, e2] =>
      if isLookupCurrHeap e2 then .seq (iselF c n temp temp e1) (.opCurrHeap op tar temp)
      else if isLookupCurrHeap e1 ∧ op ≠ .sub then .seq (iselF c n temp temp e2) (.opCurrHeap op tar temp)
      else
        match e2 with
        | .const w =>
            if c.validImm (.inl op) w then .seq (iselF c n temp temp e1) (.inst (.arith (.binop op tar temp (.imm w))))
            else if op = .add ∧ c.validImm (.inl .sub) (-w) then
              .seq (iselF c n temp temp e1) (.inst (.arith (.binop .sub tar temp (.imm (-w)))))
            else
              .seq (iselF c n temp temp e1) (.seq (.inst (.const (temp + 1) w))
                (.inst (.arith (.binop op tar temp (.reg (temp + 1))))))
        | _ =>
            .seq (iselF c n temp temp e1) (.seq (iselF c n (temp + 1) (temp + 1) e2)
              (.inst (.arith (.binop op tar temp (.reg (temp + 1))))))
  | n + 1, tar, temp, .shift sh exp e1 =>
      match e1 with
      | .const shiftLen =>
          if shiftLen.toNat < 64 then
            if shiftLen.toNat = 0 then .seq (iselF c n temp temp exp) (.move 0 [(tar, temp)])
            else .seq (iselF c n temp temp exp) (.inst (.arith (.shift sh tar temp (.imm (BitVec.ofNat 64 shiftLen.toNat)))))
          else .inst (.const tar 0)
      | _ =>
          .seq (iselF c n temp temp exp) (.seq (iselF c n (temp + 1) (temp + 1) e1)
            (.inst (.arith (.shift sh tar temp (.reg (temp + 1))))))
  | _ + 1, _, _, _ => .skip

theorem iselF_eq (c : Compiler.Encoders.Asm.AsmConfigExact 64) :
    ∀ (n tar temp : Nat) (e : WordLangExpHOL (BitVec 64)), sizeOf e < n → iselF c n tar temp e = instSelectExp c tar temp e
  | 0, _, _, e, h => absurd h (Nat.not_lt_zero _)
  | n + 1, tar, temp, e, h => by
    rw [instSelectExp.eq_def]
    cases e with
    | load exp =>
      simp only [iselF]
      split
      · rename_i exp' w
        dsimp only
        split_ifs
        · rw [iselF_eq c n temp temp exp' (by simp at h; omega)]
        · rw [iselF_eq c n temp temp _ (by simp only [WordLangExpHOL.load.sizeOf_spec] at h; omega)]
      · rename_i hx
        split
        · exfalso; simp_all
        · rw [iselF_eq c n temp temp exp (by simp at h; omega)]
    | op op args =>
      rcases args with _ | ⟨e1, _ | ⟨e2, _ | ⟨e3, rest⟩⟩⟩
      · simp only [iselF]
      · simp only [iselF]
      · simp only [iselF]
        have i1 := fun a b => iselF_eq c n a b e1 (by simp at h; omega)
        have i2 := fun a b => iselF_eq c n a b e2 (by simp at h; omega)
        split_ifs
        · rw [i1]
        · rw [i2]
        · split
          · simp only
            split_ifs <;> rw [i1]
          · split
            · exfalso; simp_all
            · rw [i1, i2]
      · simp only [iselF]
    | shift sh exp e1 =>
      simp only [iselF]
      have i1 := fun a b => iselF_eq c n a b exp (by simp at h; omega)
      have i2 := fun a b => iselF_eq c n a b e1 (by simp at h; omega)
      split
      · simp only
        split_ifs <;> first | rfl | rw [i1]
      · split
        · exfalso; simp_all
        · rw [i1, i2]
    | const _ | var _ | lookup _ => simp only [iselF]

noncomputable def pullX (e : WordLangExpHOL (BitVec 64)) : WordLangExpHOL (BitVec 64) := pullF (sizeOf e + 1) e
noncomputable def flattenX (e : WordLangExpHOL (BitVec 64)) : WordLangExpHOL (BitVec 64) := flattenF (sizeOf e + 1) e
noncomputable def iselExpX (c : Compiler.Encoders.Asm.AsmConfigExact 64) (tar temp : Nat) (e : WordLangExpHOL (BitVec 64)) :
    WordLangProgHOL (BitVec 64) := iselF c (sizeOf e + 1) tar temp e
noncomputable def cfpX (e : WordLangExpHOL (BitVec 64)) (cs : Spt (BitVec 64)) : WordLangExpHOL (BitVec 64) :=
  cfpF (sizeOf e + 1) e cs

theorem pullX_eq (e : WordLangExpHOL (BitVec 64)) : pullX e = pullExpExecutable e := pullF_eq _ e (Nat.lt_succ_self _)
theorem flattenX_eq (e : WordLangExpHOL (BitVec 64)) : flattenX e = flattenExp e :=
  flattenF_eq _ e (Nat.lt_succ_self _)
theorem iselExpX_eq (c : Compiler.Encoders.Asm.AsmConfigExact 64) (tar temp : Nat) (e : WordLangExpHOL (BitVec 64)) :
    iselExpX c tar temp e = instSelectExp c tar temp e := iselF_eq c _ tar temp e (Nat.lt_succ_self _)
theorem cfpX_eq (e : WordLangExpHOL (BitVec 64)) (cs : Spt (BitVec 64)) : cfpX e cs = WordSimp.constFpExp e cs :=
  cfpF_eq _ e cs (Nat.lt_succ_self _)

/-- Kernel-evaluable selection of an expression statement (as `instSelectExecutable`). -/
noncomputable def iselStmtF (c : Compiler.Encoders.Asm.AsmConfigExact 64) (temp : Nat) :
    WordLangProgHOL (BitVec 64) → WordLangProgHOL (BitVec 64)
  | .assign v exp => iselExpX c v temp (flattenX (pullX exp))
  | .set store exp => .seq (iselExpX c temp temp (flattenX (pullX exp))) (.set store (.var temp))
  | .store exp var =>
      match flattenX (pullX exp) with
      | .op .add [exp', .const w] =>
          if addrOffsetOk c w then .seq (iselExpX c temp temp exp') (.inst (.mem .store var (.addr temp w)))
          else .seq (iselExpX c temp temp (.op .add [exp', .const w])) (.inst (.mem .store var (.addr temp 0)))
      | e => .seq (iselExpX c temp temp e) (.inst (.mem .store var (.addr temp 0)))
  | .shareInst op v exp =>
      match flattenX (pullX exp) with
      | .op .add [exp', .const w] =>
          if ((op = .load ∨ op = .store) ∧ addrOffsetOk c w) ∨
              ((op = .load32 ∨ op = .store32) ∧ addrOffsetOk c w) ∨
              ((op = .load16 ∨ op = .store16) ∧ hwOffsetOk c w) ∨
              ((op = .load8 ∨ op = .store8) ∧ byteOffsetOk c w) then
            .seq (iselExpX c temp temp exp') (.shareInst op v (.op .add [.var temp, .const w]))
          else .seq (iselExpX c temp temp (.op .add [exp', .const w])) (.shareInst op v (.var temp))
      | e => .seq (iselExpX c temp temp e) (.shareInst op v (.var temp))
  | p => p

theorem iselStmtF_eq (c : Compiler.Encoders.Asm.AsmConfigExact 64) (temp : Nat) (p : WordLangProgHOL (BitVec 64))
    (hp : isExprStmt p = true) : iselStmtF c temp p = instSelectExecutable c temp p := by
  cases p <;> simp only [isExprStmt, Bool.false_eq_true] at hp
  case assign v e => simp only [iselStmtF, instSelectExecutable, pullX_eq, flattenX_eq, iselExpX_eq]
  case set st e => simp only [iselStmtF, instSelectExecutable, pullX_eq, flattenX_eq, iselExpX_eq]
  case store e v =>
    simp only [iselStmtF, instSelectExecutable, pullX_eq, flattenX_eq]
    generalize flattenExp (pullExpExecutable e) = E
    split
    · simp only; split_ifs <;> simp only [iselExpX_eq]
    · split
      · exfalso; simp_all
      · simp only [iselExpX_eq]
  case shareInst op v e =>
    simp only [iselStmtF, instSelectExecutable, pullX_eq, flattenX_eq]
    generalize flattenExp (pullExpExecutable e) = E
    split
    · simp only; split_ifs <;> simp only [iselExpX_eq]
    · split
      · exfalso; simp_all
      · simp only [iselExpX_eq]

/-- Kernel-evaluable `iselX`. -/
noncomputable def iselXF (c : Compiler.Encoders.Asm.AsmConfigExact 64) (p : WordLangProgHOL (BitVec 64)) : Nat :=
  (lineBound preAllocLeafBudget (iselStmtF c 0 p)).getD 0

theorem iselXF_eq (c : Compiler.Encoders.Asm.AsmConfigExact 64) (p : WordLangProgHOL (BitVec 64))
    (hp : isExprStmt p = true) : iselXF c p = iselX c p := by
  simp only [iselXF, iselX, iselStmtF_eq c 0 p hp]

#print axioms iselXF_eq
#print axioms iselF_eq
#print axioms flattenF_eq
#print axioms cfpF_eq
#print axioms pullF_eq
end InitECandidate.Runtime.FineCost
