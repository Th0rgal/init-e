import InitECandidate.Runtime.WordIselTransfer
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend

/-! Instruction selection never looks at variable names: the line bound of
selected code is unchanged when every variable is renamed to `0`. -/

mutual
/-- Every variable renamed to `0`. -/
def eraseV : WordLangExpHOL (BitVec 64) → WordLangExpHOL (BitVec 64)
  | .const w => .const w
  | .var _ => .var 0
  | .lookup st => .lookup st
  | .load e => .load (eraseV e)
  | .op o args => .op o (eraseVs args)
  | .shift sh e e1 => .shift sh (eraseV e) (eraseV e1)

def eraseVs : List (WordLangExpHOL (BitVec 64)) → List (WordLangExpHOL (BitVec 64))
  | [] => []
  | a :: as => eraseV a :: eraseVs as
end

theorem isLookupCurrHeap_eraseV (e : WordLangExpHOL (BitVec 64)) :
    WordInst.isLookupCurrHeap (eraseV e) = WordInst.isLookupCurrHeap e := by
  cases e <;> simp [eraseV, WordInst.isLookupCurrHeap]

theorem eraseV_const {e : WordLangExpHOL (BitVec 64)} {w : BitVec 64} (h : eraseV e = .const w) : e = .const w := by
  cases e <;> simp_all [eraseV]

theorem eraseV_addConst {e x : WordLangExpHOL (BitVec 64)} {w : BitVec 64}
    (h : eraseV e = .op .add [x, .const w]) : ∃ a, e = .op .add [a, .const w] ∧ x = eraseV a := by
  rcases e with _ | _ | _ | _ | ⟨o, _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩⟩ | _ <;> simp_all [eraseV, eraseVs]
  exact eraseV_const h.2.2

theorem iselExp_lineBound_eraseV (c : Compiler.Encoders.Asm.AsmConfigExact 64) (e : WordLangExpHOL (BitVec 64)) :
    ∀ (tar temp : Nat),
      lineBound preAllocLeafBudget (WordInst.instSelectExp c tar temp (eraseV e)) =
        lineBound preAllocLeafBudget (WordInst.instSelectExp c tar temp e) := by
  refine (measure (sizeOf : WordLangExpHOL (BitVec 64) → Nat)).wf.induction (C := fun e => ∀ (tar temp : Nat),
      lineBound preAllocLeafBudget (WordInst.instSelectExp c tar temp (eraseV e)) =
        lineBound preAllocLeafBudget (WordInst.instSelectExp c tar temp e)) e ?_
  intro e ih tar temp
  have ih' : ∀ e', sizeOf e' < sizeOf e → ∀ tar temp : Nat,
      lineBound preAllocLeafBudget (WordInst.instSelectExp c tar temp (eraseV e')) =
        lineBound preAllocLeafBudget (WordInst.instSelectExp c tar temp e') := fun e' h => ih e' h
  clear ih
  cases e
  case const w => rfl
  case var v =>
    simp only [eraseV]
    rw [WordInst.instSelectExp, WordInst.instSelectExp]
    simp [lineBound, isLeafProg, preAllocLeafBudget, rawMovePrice]
  case lookup st => rfl
  case load exp =>
    by_cases hf : ∃ a w, exp = .op .add [a, .const w]
    · obtain ⟨a, w, rfl⟩ := hf
      have hb := ih' (.op .add [a, .const w]) (by simp) temp temp
      simp only [eraseV, eraseVs] at hb ⊢
      rw [WordInst.instSelectExp.eq_def, WordInst.instSelectExp.eq_def]
      simp only
      split_ifs
      · exact lineBound_seq_congr (ih' a (by simp; omega) _ _) (leafX_inst _ _ rfl)
      · exact lineBound_seq_congr hb (leafX_inst _ _ rfl)
    · have hf' : ¬ ∃ x w, eraseV exp = .op .add [x, .const w] := by
        rintro ⟨x, w, hx⟩
        obtain ⟨a, rfl, -⟩ := eraseV_addConst hx
        exact hf ⟨a, w, rfl⟩
      simp only [eraseV]
      rw [WordInst.instSelectExp.eq_def, WordInst.instSelectExp.eq_def]
      simp only
      split
      · rename_i x w hx
        exact absurd ⟨x, w, hx⟩ hf'
      · split
        · exfalso
          first
            | exact hf ⟨_, _, rfl⟩
            | (rename_i h; exact hf ⟨_, _, h⟩)
        · exact lineBound_seq_congr (ih' exp (by simp) _ _) (leafX_inst _ _ rfl)
  case op op args =>
    rcases args with _ | ⟨e1, _ | ⟨e2, _ | ⟨e3, rest⟩⟩⟩
    · rfl
    · simp only [eraseV, eraseVs]
      rw [WordInst.instSelectExp.eq_def, WordInst.instSelectExp.eq_def]
    · simp only [eraseV, eraseVs]
      rw [WordInst.instSelectExp.eq_def, WordInst.instSelectExp.eq_def]
      simp only [isLookupCurrHeap_eraseV]
      split_ifs
      · exact lineBound_seq_congr (ih' e1 (by simp; omega) _ _) rfl
      · exact lineBound_seq_congr (ih' e2 (by simp; omega) _ _) rfl
      · split
        · rename_i w hw
          rw [eraseV_const hw]
          simp only
          split_ifs
          · exact lineBound_seq_congr (ih' e1 (by simp; omega) _ _) rfl
          · exact lineBound_seq_congr (ih' e1 (by simp; omega) _ _) rfl
          · exact lineBound_seq_congr (ih' e1 (by simp; omega) _ _) rfl
        · rename_i hne
          split
          · exfalso; exact hne _ rfl
          · exact lineBound_seq_congr (ih' e1 (by simp; omega) _ _)
              (lineBound_seq_congr (ih' e2 (by simp; omega) _ _) rfl)
    · simp only [eraseV, eraseVs]
      rw [WordInst.instSelectExp.eq_def, WordInst.instSelectExp.eq_def]
  case shift sh exp e1 =>
    simp only [eraseV]
    rw [WordInst.instSelectExp.eq_def, WordInst.instSelectExp.eq_def]
    simp only
    split
    · rename_i w hw
      rw [eraseV_const hw]
      simp only
      split_ifs
      · exact lineBound_seq_congr (ih' exp (by simp; omega) _ _) rfl
      · exact lineBound_seq_congr (ih' exp (by simp; omega) _ _) rfl
      · rfl
    · rename_i hne
      split
      · exfalso; exact hne _ rfl
      · exact lineBound_seq_congr (ih' exp (by simp; omega) _ _)
          (lineBound_seq_congr (ih' e1 (by simp) _ _) rfl)

theorem eraseVs_map {α : Type} (f g : α → WordLangExpHOL (BitVec 64)) :
    ∀ (l : List α), (∀ a ∈ l, eraseV (f a) = eraseV (g a)) → eraseVs (l.map f) = eraseVs (l.map g)
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.map_cons, eraseVs]
    rw [h a (by simp), eraseVs_map f g l (fun b hb => h b (by simp [hb]))]

/-- Compiled Loop expressions differ between contexts only in variable names. -/
theorem eraseV_compExp (ctxt ctxt' : Spt Nat) (e : HolLoopExp 64) :
    eraseV (LoopToWord.compExpHOL ctxt e) = eraseV (LoopToWord.compExpHOL ctxt' e) := by
  refine (measure (sizeOf : HolLoopExp 64 → Nat)).wf.induction (C := fun e =>
    eraseV (LoopToWord.compExpHOL ctxt e) = eraseV (LoopToWord.compExpHOL ctxt' e)) e ?_
  intro e ih
  cases e <;> rw [LoopToWord.compExpHOL, LoopToWord.compExpHOL] <;> simp only [eraseV]
  case load a => rw [ih a (by show sizeOf a < _; simp)]
  case shift sh a b => rw [ih a (by show sizeOf a < _; simp; omega), ih b (by show sizeOf b < _; simp)]
  case op o args =>
    rw [eraseVs_map _ _ args (fun a ha => ih a (by
      have := List.sizeOf_lt_of_mem ha
      show sizeOf a < _; simp; omega))]

theorem iselExp_lineBound_ctxt (c : Compiler.Encoders.Asm.AsmConfigExact 64) (ctxt ctxt' : Spt Nat)
    (e : HolLoopExp 64) (tar temp tar' temp' : Nat) :
    lineBound preAllocLeafBudget (WordInst.instSelectExp c tar temp (LoopToWord.compExpHOL ctxt e)) =
      lineBound preAllocLeafBudget (WordInst.instSelectExp c tar' temp' (LoopToWord.compExpHOL ctxt' e)) := by
  rw [← iselExp_lineBound_eraseV, eraseV_compExp ctxt ctxt', iselExp_lineBound_eraseV,
    iselExp_lineBound_regs c _ tar' temp' tar temp]


/-! Erasure commutes with the selector's expression preprocessing
(`pullExpExecutable`, `flattenExp`): both treat variables as opaque atoms. -/

theorem eraseVs_eq_map : ∀ l : List (WordLangExpHOL (BitVec 64)), eraseVs l = l.map eraseV
  | [] => rfl
  | a :: l => by simp only [eraseVs, List.map_cons, eraseVs_eq_map l]

theorem isConst_eraseV (e : WordLangExpHOL (BitVec 64)) : WordInst.isConst (eraseV e) = WordInst.isConst e := by
  cases e <;> rfl

theorem rmConst_eraseV (e : WordLangExpHOL (BitVec 64)) : WordInst.rmConst (eraseV e) = WordInst.rmConst e := by
  cases e <;> rfl

theorem holPart_eraseV (P : WordLangExpHOL (BitVec 64) → Bool) (hP : ∀ e, P (eraseV e) = P e) :
    ∀ (l a b : List (WordLangExpHOL (BitVec 64))),
      holPart P (l.map eraseV) (a.map eraseV) (b.map eraseV) =
        ((holPart P l a b).1.map eraseV, (holPart P l a b).2.map eraseV)
  | [], a, b => rfl
  | h :: rst, a, b => by
    simp only [List.map_cons, holPart, hP]
    split
    · exact holPart_eraseV P hP rst (h :: a) b
    · exact holPart_eraseV P hP rst a (h :: b)

theorem convertSub_eraseV (ls : List (WordLangExpHOL (BitVec 64))) :
    eraseV (WordInst.convertSub ls) = WordInst.convertSub (ls.map eraseV) := by
  rcases ls with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rfl
  · cases a <;> rfl
  · cases a <;> cases b <;> simp [WordInst.convertSub, eraseV, eraseVs]
  · cases a <;> cases b <;> simp [WordInst.convertSub, eraseV, eraseVs_eq_map]

theorem pullOps_eraseV (op : BinOp) : ∀ (xs acc : List (WordLangExpHOL (BitVec 64))),
    (WordInst.pullOps op xs acc).map eraseV = WordInst.pullOps op (xs.map eraseV) (acc.map eraseV)
  | [], acc => rfl
  | x :: xs, acc => by
    cases x
    case op op' ls =>
      simp only [List.map_cons, eraseV, WordInst.pullOps, eraseVs_eq_map]
      split
      · rw [pullOps_eraseV op xs, List.map_append]
      · rw [pullOps_eraseV op xs]; simp [eraseV, eraseVs_eq_map]
    all_goals (simp only [List.map_cons, eraseV, WordInst.pullOps]; rw [pullOps_eraseV op xs]; rfl)

theorem reduceConst_eraseV (op : BinOp) (w : BitVec 64) (rest : List (WordLangExpHOL (BitVec 64))) :
    eraseV (WordInst.reduceConst op w rest) = WordInst.reduceConst op w (rest.map eraseV) := by
  unfold WordInst.reduceConst
  split_ifs
  · rcases rest with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp [eraseV, eraseVs_eq_map]
  · rfl
  · simp [eraseV, eraseVs_eq_map]
  · simp [eraseV, eraseVs_eq_map]

theorem optimizeNonSub_eraseV (op : BinOp) (h : op ≠ .sub) (ls : List (WordLangExpHOL (BitVec 64))) :
    eraseV (WordInst.ExecutablePullExp.optimizeNonSub op h ls) =
      WordInst.ExecutablePullExp.optimizeNonSub op h (ls.map eraseV) := by
  unfold WordInst.ExecutablePullExp.optimizeNonSub holPartition
  have hp := holPart_eraseV (fun e => WordInst.isConst e) isConst_eraseV ls [] []
  simp only [List.map_nil] at hp
  rw [hp]
  rcases holPart (fun e => WordInst.isConst e) ls [] [] with ⟨cs, ns⟩
  rcases cs with _ | ⟨c0, cs⟩
  · simp [eraseV, eraseVs_eq_map]
  · simp only [List.map_cons, List.map_map]
    rw [reduceConst_eraseV]
    simp [Function.comp_def, rmConst_eraseV]

#print axioms optimizeNonSub_eraseV

theorem map_attach_val {β : Type} (l : List (WordLangExpHOL (BitVec 64))) (f : WordLangExpHOL (BitVec 64) → β) :
    (l.attach.map fun (x : {x // x ∈ l}) => f x.1) = l.map f := by
  simp

theorem map_erase_comm (f : WordLangExpHOL (BitVec 64) → WordLangExpHOL (BitVec 64)) (l : List (WordLangExpHOL (BitVec 64)))
    (h : ∀ a ∈ l, eraseV (f a) = f (eraseV a)) : (l.map f).map eraseV = (l.map eraseV).map f := by
  simp only [List.map_map]
  exact List.map_congr_left (fun a ha => h a ha)

theorem pullExp_eraseV (e : WordLangExpHOL (BitVec 64)) :
    eraseV (WordInst.ExecutablePullExp.pullExpExecutable e) =
      WordInst.ExecutablePullExp.pullExpExecutable (eraseV e) := by
  refine (measure (sizeOf : WordLangExpHOL (BitVec 64) → Nat)).wf.induction (C := fun e =>
    eraseV (WordInst.ExecutablePullExp.pullExpExecutable e) =
      WordInst.ExecutablePullExp.pullExpExecutable (eraseV e)) e ?_
  intro e ih
  cases e
  case op o ls =>
    have ihl : ∀ a ∈ ls, eraseV (WordInst.ExecutablePullExp.pullExpExecutable a) =
        WordInst.ExecutablePullExp.pullExpExecutable (eraseV a) := fun a ha =>
      ih a (by have := List.sizeOf_lt_of_mem ha; show sizeOf a < _; simp; omega)
    simp only [eraseV, eraseVs_eq_map]
    rw [WordInst.ExecutablePullExp.pullExpExecutable, WordInst.ExecutablePullExp.pullExpExecutable]
    by_cases hs : o = .sub
    · simp only [hs, dif_pos, map_attach_val, convertSub_eraseV]
      rw [map_erase_comm _ ls ihl]
    · simp only [hs, dif_neg, not_false_eq_true]
      rcases ls with _ | ⟨x, _ | ⟨y, rest⟩⟩
      · simp only [List.map_nil]
        cases o <;> rfl
      · exact ihl x (by simp)
      · simp only [List.map_cons, map_attach_val, optimizeNonSub_eraseV, pullOps_eraseV, List.map_nil]
        rw [ihl x (by simp), ihl y (by simp), map_erase_comm _ rest (fun a ha => ihl a (by simp [ha]))]
  case load a =>
    simp only [eraseV]
    rw [WordInst.ExecutablePullExp.pullExpExecutable, WordInst.ExecutablePullExp.pullExpExecutable]
    simp only [eraseV, ih a (by show sizeOf a < _; simp)]
  case shift sh a b =>
    simp only [eraseV]
    rw [WordInst.ExecutablePullExp.pullExpExecutable, WordInst.ExecutablePullExp.pullExpExecutable]
    simp only [eraseV, ih a (by show sizeOf a < _; simp; omega), ih b (by show sizeOf b < _; simp)]
  all_goals
    simp only [eraseV]
    rw [WordInst.ExecutablePullExp.pullExpExecutable.eq_def]
    try rw [WordInst.ExecutablePullExp.pullExpExecutable.eq_def]
    simp [eraseV]

#print axioms pullExp_eraseV

theorem flattenExp_eraseV (e : WordLangExpHOL (BitVec 64)) :
    eraseV (WordInst.flattenExp e) = WordInst.flattenExp (eraseV e) := by
  refine (measure (sizeOf : WordLangExpHOL (BitVec 64) → Nat)).wf.induction (C := fun e =>
    eraseV (WordInst.flattenExp e) = WordInst.flattenExp (eraseV e)) e ?_
  intro e ih
  cases e
  case op o ls =>
    have ihl : ∀ a ∈ ls, eraseV (WordInst.flattenExp a) = WordInst.flattenExp (eraseV a) := fun a ha =>
      ih a (by have := List.sizeOf_lt_of_mem ha; show sizeOf a < _; simp; omega)
    simp only [eraseV, eraseVs_eq_map]
    by_cases hs : o = .sub
    · subst hs
      rw [WordInst.flattenExp, WordInst.flattenExp]
      simp only [eraseV, eraseVs_eq_map, map_attach_val]
      rw [map_erase_comm _ ls ihl]
    · rcases ls with _ | ⟨x, _ | ⟨y, rest⟩⟩
      · rw [WordInst.flattenExp.eq_def, WordInst.flattenExp.eq_def]
        cases o <;> first | exact absurd rfl hs | rfl
      · rw [WordInst.flattenExp.eq_def]
        try rw [WordInst.flattenExp.eq_def]
        cases o <;> first | exact absurd rfl hs | exact ihl x (by simp)
      · have hrest := ih (.op o (y :: rest)) (by show sizeOf _ < _; simp)
        simp only [eraseV, eraseVs_eq_map, List.map_cons] at hrest
        rw [WordInst.flattenExp.eq_def]
        try rw [WordInst.flattenExp.eq_def]
        cases o <;> first
          | exact absurd rfl hs
          | (simp only [eraseV, eraseVs, List.map_cons]
             rw [hrest, ihl x (by simp)])
  case load a =>
    rw [WordInst.flattenExp.eq_def]
    try rw [WordInst.flattenExp.eq_def]
    simp only [eraseV, ih a (by show sizeOf a < _; simp)]
  case shift sh a b =>
    rw [WordInst.flattenExp.eq_def]
    try rw [WordInst.flattenExp.eq_def]
    simp only [eraseV, ih a (by show sizeOf a < _; simp; omega), ih b (by show sizeOf b < _; simp)]
  all_goals
    simp only [eraseV]
    rw [WordInst.flattenExp.eq_def]
    try rw [WordInst.flattenExp.eq_def]
    simp [eraseV]

/-- The selector's preprocessed expression, erased, depends only on the erased input. -/
theorem prep_eraseV (e : WordLangExpHOL (BitVec 64)) :
    eraseV (WordInst.flattenExp (WordInst.ExecutablePullExp.pullExpExecutable e)) =
      WordInst.flattenExp (WordInst.ExecutablePullExp.pullExpExecutable (eraseV e)) := by
  rw [flattenExp_eraseV, pullExp_eraseV]

#print axioms prep_eraseV

abbrev prepE (e : WordLangExpHOL (BitVec 64)) : WordLangExpHOL (BitVec 64) :=
  WordInst.flattenExp (WordInst.ExecutablePullExp.pullExpExecutable e)

theorem prepE_erase {e e' : WordLangExpHOL (BitVec 64)} (h : eraseV e = eraseV e') :
    eraseV (prepE e) = eraseV (prepE e') := by
  simp only [prepE, prep_eraseV, h]

theorem isel_erase (c : Compiler.Encoders.Asm.AsmConfigExact 64) {a a' : WordLangExpHOL (BitVec 64)}
    (h : eraseV a = eraseV a') (tar temp tar' temp' : Nat) :
    lineBound preAllocLeafBudget (WordInst.instSelectExp c tar temp a) =
      lineBound preAllocLeafBudget (WordInst.instSelectExp c tar' temp' a') := by
  rw [← iselExp_lineBound_eraseV c a, h, iselExp_lineBound_eraseV, iselExp_lineBound_regs c a' tar temp tar' temp']

/-- An address match `op add [x, const w]` on one side forces it on the other. -/
theorem addConst_erase {E E' x : WordLangExpHOL (BitVec 64)} {w : BitVec 64}
    (h : eraseV E = eraseV E') (hE : E = .op .add [x, .const w]) :
    ∃ x', E' = .op .add [x', .const w] ∧ eraseV x = eraseV x' := by
  subst hE
  have h' : eraseV E' = .op .add [eraseV x, .const w] := by rw [← h]; rfl
  obtain ⟨a, rfl, hx⟩ := eraseV_addConst h'
  exact ⟨a, rfl, hx⟩

theorem iselX_assign (c : Compiler.Encoders.Asm.AsmConfigExact 64) {e e' : WordLangExpHOL (BitVec 64)}
    (h : eraseV e = eraseV e') (v v' : Nat) : iselX c (.assign v e) = iselX c (.assign v' e') := by
  simp only [iselX, WordInst.instSelectExecutable]
  rw [isel_erase c (prepE_erase h) v 0 v' 0]

theorem iselX_set (c : Compiler.Encoders.Asm.AsmConfigExact 64) {e e' : WordLangExpHOL (BitVec 64)}
    (h : eraseV e = eraseV e') (st : WordStoreHOL) : iselX c (.set st e) = iselX c (.set st e') := by
  simp only [iselX, WordInst.instSelectExecutable]
  rw [lineBound_seq_congr (isel_erase c (prepE_erase h) 0 0 0 0).symm rfl]

theorem iselX_store (c : Compiler.Encoders.Asm.AsmConfigExact 64) {e e' : WordLangExpHOL (BitVec 64)}
    (h : eraseV e = eraseV e') (v v' : Nat) : iselX c (.store e v) = iselX c (.store e' v') := by
  have hp : eraseV (WordInst.flattenExp (WordInst.ExecutablePullExp.pullExpExecutable e)) =
      eraseV (WordInst.flattenExp (WordInst.ExecutablePullExp.pullExpExecutable e')) := prepE_erase h
  simp only [iselX, WordInst.instSelectExecutable]
  congr 1
  generalize WordInst.flattenExp (WordInst.ExecutablePullExp.pullExpExecutable e) = E at hp ⊢
  generalize WordInst.flattenExp (WordInst.ExecutablePullExp.pullExpExecutable e') = E' at hp ⊢
  by_cases hf : ∃ x w, E = .op .add [x, .const w]
  · obtain ⟨x, w, rfl⟩ := hf
    obtain ⟨x', rfl, hx⟩ := addConst_erase hp rfl
    simp only
    split_ifs
    · exact lineBound_seq_congr (isel_erase c hx 0 0 0 0) (leafX_inst _ _ rfl)
    · exact lineBound_seq_congr (isel_erase c hp 0 0 0 0) (leafX_inst _ _ rfl)
  · have hf' : ¬ ∃ x w, E' = .op .add [x, .const w] := by
      rintro ⟨x', w, hE'⟩
      obtain ⟨x, hE, -⟩ := addConst_erase hp.symm hE'
      exact hf ⟨x, w, hE⟩
    split
    · exact absurd ⟨_, _, rfl⟩ hf
    · split
      · exact absurd ⟨_, _, rfl⟩ hf'
      · exact lineBound_seq_congr (isel_erase c hp 0 0 0 0) (leafX_inst _ _ rfl)

theorem iselX_share (c : Compiler.Encoders.Asm.AsmConfigExact 64) {e e' : WordLangExpHOL (BitVec 64)}
    (h : eraseV e = eraseV e') (op : WordMemOp) (v v' : Nat) :
    iselX c (.shareInst op v e) = iselX c (.shareInst op v' e') := by
  have hp : eraseV (WordInst.flattenExp (WordInst.ExecutablePullExp.pullExpExecutable e)) =
      eraseV (WordInst.flattenExp (WordInst.ExecutablePullExp.pullExpExecutable e')) := prepE_erase h
  simp only [iselX, WordInst.instSelectExecutable]
  congr 1
  generalize WordInst.flattenExp (WordInst.ExecutablePullExp.pullExpExecutable e) = E at hp ⊢
  generalize WordInst.flattenExp (WordInst.ExecutablePullExp.pullExpExecutable e') = E' at hp ⊢
  have leafS : ∀ a b : WordLangExpHOL (BitVec 64), ∀ u u' : Nat,
      lineBound preAllocLeafBudget (.shareInst op u' b) = lineBound preAllocLeafBudget (.shareInst op u a) := by
    intros; simp [lineBound, isLeafProg, preAllocLeafBudget, WordToStack.refinedWordStackLeafBudget]
  by_cases hf : ∃ x w, E = .op .add [x, .const w]
  · obtain ⟨x, w, rfl⟩ := hf
    obtain ⟨x', rfl, hx⟩ := addConst_erase hp rfl
    simp only
    split_ifs
    · exact lineBound_seq_congr (isel_erase c hx 0 0 0 0) (leafS _ _ _ _)
    · exact lineBound_seq_congr (isel_erase c hp 0 0 0 0) (leafS _ _ _ _)
  · have hf' : ¬ ∃ x w, E' = .op .add [x, .const w] := by
      rintro ⟨x', w, hE'⟩
      obtain ⟨x, hE, -⟩ := addConst_erase hp.symm hE'
      exact hf ⟨x, w, hE⟩
    split
    · exact absurd ⟨_, _, rfl⟩ hf
    · split
      · exact absurd ⟨_, _, rfl⟩ hf'
      · exact lineBound_seq_congr (isel_erase c hp 0 0 0 0) (leafS _ _ _ _)

#print axioms iselX_store
#print axioms iselX_share
#print axioms iselExp_lineBound_eraseV
#print axioms iselExp_lineBound_ctxt
end InitECandidate.Runtime.FineCost
