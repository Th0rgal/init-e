import InitECandidate.Runtime.CrepSelTight
import InitECandidate.Runtime.CrepSimpIdem
namespace InitECandidate.Runtime.FineCost
open Flapjack

/-! Variable erasure: a Crep expression with every variable index set to 0.
The pattern-aware selector price, the node-cost prices and `simp_exp` see
only the erased structure, so compiled code that differs only in variable
numbering has the same prices. -/

def crepErase : CrepExpHOL 64 → CrepExpHOL 64
  | .var _ => .var 0
  | .load a => .load (crepErase a)
  | .load32 a => .load32 (crepErase a)
  | .loadByte a => .loadByte (crepErase a)
  | .op o args => .op o (args.attach.map (fun ⟨a, _⟩ => crepErase a))
  | .crepOp o args => .crepOp o (args.attach.map (fun ⟨a, _⟩ => crepErase a))
  | .shift s a b => .shift s (crepErase a) (crepErase b)
  | .cmp o a b => .cmp o (crepErase a) (crepErase b)
  | e => e
termination_by e => sizeOf e
decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial | simp_wf

@[simp] theorem crepErase_var (n : Nat) : crepErase (.var n) = .var 0 := by simp [crepErase]
@[simp] theorem crepErase_const (w : BitVec 64) : crepErase (.const w) = .const w := by simp [crepErase]
@[simp] theorem crepErase_loadGlob (a : BitVec 5) : crepErase (.loadGlob a) = .loadGlob a := by simp [crepErase]
@[simp] theorem crepErase_baseAddr : crepErase .baseAddr = .baseAddr := by simp [crepErase]
@[simp] theorem crepErase_topAddr : crepErase .topAddr = .topAddr := by simp [crepErase]
@[simp] theorem crepErase_load (a : CrepExpHOL 64) : crepErase (.load a) = .load (crepErase a) := by
  simp [crepErase]
@[simp] theorem crepErase_load32 (a : CrepExpHOL 64) : crepErase (.load32 a) = .load32 (crepErase a) := by
  simp [crepErase]
@[simp] theorem crepErase_loadByte (a : CrepExpHOL 64) : crepErase (.loadByte a) = .loadByte (crepErase a) := by
  simp [crepErase]
@[simp] theorem crepErase_op (o : BinOp) (args : List (CrepExpHOL 64)) :
    crepErase (.op o args) = .op o (args.map crepErase) := by
  rw [crepErase]; simp [List.map_attach_eq_pmap]
@[simp] theorem crepErase_crepOp (o : CrepOp) (args : List (CrepExpHOL 64)) :
    crepErase (.crepOp o args) = .crepOp o (args.map crepErase) := by
  rw [crepErase]; simp [List.map_attach_eq_pmap]
@[simp] theorem crepErase_shift (s : Shift) (a b : CrepExpHOL 64) :
    crepErase (.shift s a b) = .shift s (crepErase a) (crepErase b) := by simp [crepErase]
@[simp] theorem crepErase_cmp (o : Cmp) (a b : CrepExpHOL 64) :
    crepErase (.cmp o a b) = .cmp o (crepErase a) (crepErase b) := by simp [crepErase]

theorem crepErase_safeC (o : BinOp) (a : CrepExpHOL 64) : safeC o (crepErase a) = safeC o a := by
  cases a <;> simp [safeC]

theorem crepErase_const_iff (e : CrepExpHOL 64) (w : BitVec 64) :
    crepErase e = .const w ↔ e = .const w := by
  cases e <;> simp

theorem crepErase_destConst (e : CrepExpHOL 64) : crepDestConstHOL (crepErase e) = crepDestConstHOL e := by
  cases e <;> simp [crepDestConstHOL]

mutual
  theorem selNodePrice_erase : ∀ e : CrepExpHOL 64, selNodePrice (crepErase e) = selNodePrice e
    | .const _ | .var _ | .loadGlob _ | .baseAddr | .topAddr => by simp [selNodePrice]
    | .load a | .load32 a | .loadByte a => by simp [selNodePrice, selNodePrice_erase a]
    | .op _ args | .crepOp _ args => by simp [selNodePrice, selPriceList_erase args]
    | .shift _ l r | .cmp _ l r => by simp [selNodePrice, selNodePrice_erase l, selNodePrice_erase r]
  termination_by e => sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  theorem selPriceList_erase : ∀ es : List (CrepExpHOL 64), selPriceList (es.map crepErase) = selPriceList es
    | [] => by simp [selPriceList]
    | e :: es => by simp [selPriceList, selNodePrice_erase e, selPriceList_erase es]
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

theorem nodeT_erase (c : Compiler.Encoders.Asm.AsmConfigExact 64) (e : CrepExpHOL 64) :
    nodeT c (crepErase e) = nodeT c e := by
  refine (measure (sizeOf : CrepExpHOL 64 → Nat)).wf.induction (C := fun e => nodeT c (crepErase e) = nodeT c e) e ?_
  intro e ih
  cases e with
  | const w => simp
  | var v => simp only [crepErase_var]; rw [nodeT.eq_2, nodeT.eq_2]
  | loadGlob a => simp
  | baseAddr => simp
  | topAddr => simp
  | load x =>
    have hx := ih x (by show sizeOf x < _; simp)
    by_cases hs : ∃ a w, x = .op .sub [a, .const w]
    · obtain ⟨a, w, rfl⟩ := hs
      have ha := ih a (by show sizeOf a < _; simp; omega)
      simp only [crepErase_load, crepErase_op, List.map_cons, List.map_nil, crepErase_const] at hx ⊢
      rw [nodeT.eq_6, nodeT.eq_6, ha, hx]
    · by_cases hd : ∃ a w, x = .op .add [a, .const w]
      · obtain ⟨a, w, rfl⟩ := hd
        have ha := ih a (by show sizeOf a < _; simp; omega)
        simp only [crepErase_load, crepErase_op, List.map_cons, List.map_nil, crepErase_const] at hx ⊢
        rw [nodeT.eq_7, nodeT.eq_7, ha, hx, crepErase_safeC]
      · have hs' : ∀ a w, crepErase x = .op .sub [a, .const w] → False := by
          intro a w h
          cases x <;> simp at h
          rename_i o args
          rcases args with _ | ⟨p, _ | ⟨q, _ | _⟩⟩ <;> simp at h
          obtain ⟨rfl, rfl, hq⟩ := h
          rw [crepErase_const_iff] at hq
          exact hs ⟨p, w, by rw [hq]⟩
        have hd' : ∀ a w, crepErase x = .op .add [a, .const w] → False := by
          intro a w h
          cases x <;> simp at h
          rename_i o args
          rcases args with _ | ⟨p, _ | ⟨q, _ | _⟩⟩ <;> simp at h
          obtain ⟨rfl, rfl, hq⟩ := h
          rw [crepErase_const_iff] at hq
          exact hd ⟨p, w, by rw [hq]⟩
        simp only [crepErase_load]
        rw [nodeT.eq_8 c (crepErase x) hs' hd', nodeT.eq_8 c x (fun a w h => hs ⟨a, w, h⟩)
          (fun a w h => hd ⟨a, w, h⟩), hx]
  | load32 x =>
    have := ih x (by show sizeOf x < _; simp); simp only [crepErase_load32]; rw [nodeT.eq_9, nodeT.eq_9, this]
  | loadByte x =>
    have := ih x (by show sizeOf x < _; simp); simp only [crepErase_loadByte]; rw [nodeT.eq_10, nodeT.eq_10, this]
  | shift s a b =>
    have ha := ih a (by show sizeOf a < _; simp; omega)
    by_cases hb : ∃ n, b = .const n
    · obtain ⟨n, rfl⟩ := hb
      simp only [crepErase_shift, crepErase_const]; rw [nodeT.eq_11, nodeT.eq_11, ha]
    · have hb' := ih b (by show sizeOf b < _; simp)
      have hb2 : ∀ n, crepErase b = .const n → False := fun n h => hb ⟨n, (crepErase_const_iff b n).mp h⟩
      simp only [crepErase_shift]
      rw [nodeT.eq_12 c s _ _ hb2, nodeT.eq_12 c s a b (fun n h => hb ⟨n, h⟩), ha, hb']
  | op o ls =>
    rcases ls with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
    · simp only [crepErase_op, List.map_nil]
    · simp only [crepErase_op, List.map_cons, List.map_nil]
      rw [nodeT.eq_17, nodeT.eq_17]
      all_goals first | (intros; simp_all; done) | simp [selNodePrice, selPriceList, selNodePrice_erase, selPriceList_erase]
    · have ha := ih a (by show sizeOf a < _; simp; omega)
      simp only [crepErase_op, List.map_cons, List.map_nil]
      by_cases ho : o = .sub
      · subst ho
        by_cases hb : ∃ w, b = .const w
        · obtain ⟨w, rfl⟩ := hb
          simp only [crepErase_const]; rw [nodeT.eq_13, nodeT.eq_13, ha]
        · have hbb := ih b (by show sizeOf b < _; simp; omega)
          have hb2 : ∀ w, crepErase b = .const w → False := fun w h => hb ⟨w, (crepErase_const_iff b w).mp h⟩
          rw [nodeT.eq_14 c _ _ hb2, nodeT.eq_14 c a b (fun w h => hb ⟨w, h⟩), ha, hbb]
      · by_cases hb : ∃ w, b = .const w
        · obtain ⟨w, rfl⟩ := hb
          simp only [crepErase_const]
          rw [nodeT.eq_15 c o _ w ho, nodeT.eq_15 c o a w ho, ha, crepErase_safeC]
          split_ifs
          · rfl
          · simp [selNodePrice, selPriceList, selNodePrice_erase]
        · have hbb := ih b (by show sizeOf b < _; simp; omega)
          have hb2 : ∀ w, crepErase b = .const w → False := fun w h => hb ⟨w, (crepErase_const_iff b w).mp h⟩
          rw [nodeT.eq_16 c o _ _ (fun w _ h => hb2 w h) ho hb2,
            nodeT.eq_16 c o a b (fun w _ h => hb ⟨w, h⟩) ho (fun w h => hb ⟨w, h⟩), ha, hbb,
            crepErase_safeC, crepErase_safeC]
          split_ifs
          · rfl
          · simp [selNodePrice, selPriceList, selNodePrice_erase]
    · simp only [crepErase_op, List.map_cons]
      rw [nodeT.eq_17, nodeT.eq_17]
      all_goals first | (intros; simp_all; done) | simp [selNodePrice, selPriceList, selNodePrice_erase, selPriceList_erase]
  | crepOp o xs =>
    simp only [crepErase_crepOp]
    rw [nodeT.eq_17, nodeT.eq_17]
    all_goals first | (intros; simp_all; done) | simp [selNodePrice, selPriceList, selNodePrice_erase, selPriceList_erase]
  | cmp o x y =>
    simp only [crepErase_cmp]
    rw [nodeT.eq_17, nodeT.eq_17]
    all_goals first | (intros; simp_all; done) | simp [selNodePrice, selPriceList, selNodePrice_erase, selPriceList_erase]

theorem crepErase_mulConst (x : CrepExpHOL 64) (c : BitVec 64) :
    crepErase (crepMulConstHOL x c) = crepMulConstHOL (crepErase x) c := by
  unfold crepMulConstHOL
  by_cases c0 : c = 0
  · simp [c0]
  by_cases c1 : c = 1
  · simp [c0, c1]
  simp only [c0, c1, if_false]
  cases crepDest2ExpHOL 0 c <;> simp

theorem crepSimp_erase : ∀ e : CrepExpHOL 64, crepSimpExpHOL (crepErase e) = crepErase (crepSimpExpHOL e)
  | .crepOp op es => by
    have ih : ∀ e ∈ es, crepSimpExpHOL (crepErase e) = crepErase (crepSimpExpHOL e) :=
      fun e _ => crepSimp_erase e
    have listIh : (es.map crepErase).map crepSimpExpHOL = (es.map crepSimpExpHOL).map crepErase := by
      rw [List.map_map, List.map_map]
      exact List.map_congr_left (fun e h => ih e h)
    simp only [crepErase_crepOp]
    by_cases two : ∃ a b, op = .mul ∧ es = [a, b]
    · obtain ⟨a, b, rfl, rfl⟩ := two
      have ha := ih a (by simp)
      have hb := ih b (by simp)
      simp only [List.map_cons, List.map_nil]
      rw [crepSimpExpHOL.eq_1 [crepErase a, crepErase b] (crepSimpExpHOL (crepErase a))
        (crepSimpExpHOL (crepErase b)) (by simp),
        crepSimpExpHOL.eq_1 [a, b] (crepSimpExpHOL a) (crepSimpExpHOL b) (by simp), ha, hb,
        crepErase_destConst, crepErase_destConst]
      cases crepDestConstHOL (crepSimpExpHOL a) <;> cases crepDestConstHOL (crepSimpExpHOL b)
      · simp only []
        rw [crepErase_crepOp]
        simp only [List.map_cons, List.map_nil, ha, hb]
      · simp only []; rw [crepErase_mulConst]
      · simp only []; rw [crepErase_mulConst]
      · simp
    · have side : ∀ (first second : CrepExpHOL 64), op = CrepOp.mul →
          es.map crepSimpExpHOL = [first, second] → False := by
        intro first second hop hmap
        rcases es with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp at hmap
        exact two ⟨a, b, hop, rfl⟩
      have side' : ∀ (first second : CrepExpHOL 64), op = CrepOp.mul →
          (es.map crepErase).map crepSimpExpHOL = [first, second] → False := by
        intro first second hop hmap
        rcases es with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp at hmap
        exact two ⟨a, b, hop, rfl⟩
      rw [crepSimpExpHOL.eq_2 _ op side', crepSimpExpHOL.eq_2 es op side, crepErase_crepOp, listIh]
  | .load a => by simp only [crepErase_load]; rw [crepSimpExpHOL.eq_3, crepSimpExpHOL.eq_3, crepSimp_erase a]; simp
  | .load32 a => by
    simp only [crepErase_load32]; rw [crepSimpExpHOL.eq_4, crepSimpExpHOL.eq_4, crepSimp_erase a]; simp
  | .loadByte a => by
    simp only [crepErase_loadByte]; rw [crepSimpExpHOL.eq_5, crepSimpExpHOL.eq_5, crepSimp_erase a]; simp
  | .op op es => by
    have ih : ∀ e ∈ es, crepSimpExpHOL (crepErase e) = crepErase (crepSimpExpHOL e) :=
      fun e _ => crepSimp_erase e
    simp only [crepErase_op]
    rw [crepSimpExpHOL.eq_6, crepSimpExpHOL.eq_6, crepErase_op, List.map_map, List.map_map]
    congr 1
    exact List.map_congr_left (fun e h => ih e h)
  | .cmp op a b => by
    simp only [crepErase_cmp]
    rw [crepSimpExpHOL.eq_7, crepSimpExpHOL.eq_7, crepSimp_erase a, crepSimp_erase b]; simp
  | .shift op a b => by
    simp only [crepErase_shift]
    rw [crepSimpExpHOL.eq_8, crepSimpExpHOL.eq_8, crepSimp_erase a, crepSimp_erase b]; simp
  | .const _ | .var _ | .loadGlob _ | .baseAddr | .topAddr => by simp [crepSimpExpHOL]
termination_by e => sizeOf e
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial | simp_wf

#print axioms crepSimp_erase

#print axioms nodeT_erase
#print axioms selNodePrice_erase
end InitECandidate.Runtime.FineCost
