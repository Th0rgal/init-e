import InitECandidate.Runtime.CrepWorkFSimp
namespace InitECandidate.Runtime.FineCost
open Flapjack

/-! `crep_arith$simp_exp` is idempotent. -/

theorem crepSimp_const (w : BitVec 64) : crepSimpExpHOL (.const w : CrepExpHOL 64) = .const w := by
  simp [crepSimpExpHOL]

/-- A multiplication by a constant of an already simplified, non-constant
operand is a fixed point. -/
theorem crepSimp_mulConst_fixed (x : CrepExpHOL 64) (c : BitVec 64)
    (hx : crepSimpExpHOL x = x) (nonConst : crepDestConstHOL x = none) :
    crepSimpExpHOL (crepMulConstHOL x c) = crepMulConstHOL x c := by
  unfold crepMulConstHOL
  by_cases c0 : c = 0
  · rw [if_pos c0, crepSimp_const]
  rw [if_neg c0]
  by_cases c1 : c = 1
  · rw [if_pos c1]; exact hx
  rw [if_neg c1]
  cases hd : crepDest2ExpHOL 0 c with
  | none =>
    simp only []
    rw [crepSimpExpHOL.eq_1 [x, .const c] x (.const c) (by simp [hx, crepSimp_const])]
    rw [nonConst]
    simp only [crepDestConstHOL]
    unfold crepMulConstHOL
    rw [if_neg c0, if_neg c1, hd]
  | some k =>
    simp only []
    rw [crepSimpExpHOL.eq_8, hx, crepSimp_const]

theorem crepSimp_idem : ∀ e : CrepExpHOL 64, crepSimpExpHOL (crepSimpExpHOL e) = crepSimpExpHOL e
  | .crepOp op es => by
    have ih : ∀ e ∈ es, crepSimpExpHOL (crepSimpExpHOL e) = crepSimpExpHOL e :=
      fun e _ => crepSimp_idem e
    have listIh : (es.map crepSimpExpHOL).map crepSimpExpHOL = es.map crepSimpExpHOL := by
      rw [List.map_map]
      exact List.map_congr_left (fun e h => ih e h)
    by_cases two : ∃ a b, op = .mul ∧ es = [a, b]
    · obtain ⟨a, b, rfl, rfl⟩ := two
      have ha := ih a (by simp)
      have hb := ih b (by simp)
      rw [crepSimpExpHOL.eq_1 [a, b] (crepSimpExpHOL a) (crepSimpExpHOL b) (by simp)]
      cases da : crepDestConstHOL (crepSimpExpHOL a) <;> cases db : crepDestConstHOL (crepSimpExpHOL b)
      · simp only []
        rw [crepSimpExpHOL.eq_1 ([a, b].map crepSimpExpHOL) (crepSimpExpHOL a) (crepSimpExpHOL b)
          (by simp [ha, hb])]
        simp only [da, db]
        rw [listIh]
      · rename_i constant
        exact crepSimp_mulConst_fixed _ constant ha da
      · rename_i constant
        exact crepSimp_mulConst_fixed _ constant hb db
      · simp only []
        exact crepSimp_const _
    · have side : ∀ (first second : CrepExpHOL 64), op = CrepOp.mul →
          es.map crepSimpExpHOL = [first, second] → False := by
        intro first second hop hmap
        rcases es with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp at hmap
        exact two ⟨a, b, hop, rfl⟩
      have side' : ∀ (first second : CrepExpHOL 64), op = CrepOp.mul →
          (es.map crepSimpExpHOL).map crepSimpExpHOL = [first, second] → False := by
        intro first second hop hmap
        rw [listIh] at hmap
        exact side first second hop hmap
      rw [crepSimpExpHOL.eq_2 es op side, crepSimpExpHOL.eq_2 _ op side', listIh]
  | .load a => by
    rw [crepSimpExpHOL.eq_3, crepSimpExpHOL.eq_3, crepSimp_idem a]
  | .load32 a => by
    rw [crepSimpExpHOL.eq_4, crepSimpExpHOL.eq_4, crepSimp_idem a]
  | .loadByte a => by
    rw [crepSimpExpHOL.eq_5, crepSimpExpHOL.eq_5, crepSimp_idem a]
  | .op op es => by
    have ih : ∀ e ∈ es, crepSimpExpHOL (crepSimpExpHOL e) = crepSimpExpHOL e :=
      fun e _ => crepSimp_idem e
    rw [crepSimpExpHOL.eq_6, crepSimpExpHOL.eq_6, List.map_map]
    congr 1
    exact List.map_congr_left (fun e h => ih e h)
  | .cmp op a b => by
    rw [crepSimpExpHOL.eq_7, crepSimpExpHOL.eq_7, crepSimp_idem a, crepSimp_idem b]
  | .shift op a b => by
    rw [crepSimpExpHOL.eq_8, crepSimpExpHOL.eq_8, crepSimp_idem a, crepSimp_idem b]
  | .const _ | .var _ | .loadGlob _ | .baseAddr | .topAddr => by simp [crepSimpExpHOL]
termination_by e => sizeOf e
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial | simp_wf

#print axioms crepSimp_idem
end InitECandidate.Runtime.FineCost
