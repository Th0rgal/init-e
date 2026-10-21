import InitECandidate.Runtime.CrepToLoopLocalBound
namespace InitECandidate.Runtime.FineCost
open Flapjack

/-! Native price of a Crep expression: the native Loop code work and residual
value of `crep_to_loop$compile_exp`, independent of the compile context, at the
checked `WordToStack` caps. Argument moves are priced by the list price. -/

mutual
  def loopNodePrice : CrepExpHOL 64 → Nat
    | .const _ => 19
    | .var _ | .loadGlob _ | .baseAddr => 14
    | .topAddr => 81
    | .load address => loopNodePrice address + 21
    | .load32 address | .loadByte address => loopNodePrice address + 49
    | .op _ args => loopPriceList args + 28 * (args.length - 1) + 19 * (1 - (args.length - 1))
    | .crepOp _ args => loopPriceList args + 57
    | .shift _ left right => loopNodePrice left + loopNodePrice right + 32
    | .cmp _ left right => loopNodePrice left + loopNodePrice right + 70
  termination_by e => sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  def loopPriceList : List (CrepExpHOL 64) → Nat
    | [] => 0
    | head :: tail => loopNodePrice head + loopPriceList tail
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

theorem price_compileExps_length (context : CrepToLoopContextExact) :
    ∀ (es : List (CrepExpHOL 64)) (tmp : Nat) (live : NumSet),
      (compileExpsHOLExact context tmp live es).2.1.length = es.length
  | [], _, _ => by simp [compileExpsHOLExact]
  | e :: es, tmp, live => by
    rcases hA : compileExpHOLExact context tmp live e with ⟨c, v, n, o⟩
    rcases hB : compileExpsHOLExact context n o es with ⟨c', vs, n', o'⟩
    have := price_compileExps_length context es n o
    rw [hB] at this
    simp only [compileExpsHOLExact, hA, hB, List.length_cons]
    simp only [] at this
    omega

mutual
  theorem crep_to_loop_price_work (context : CrepToLoopContextExact) (tmp : Nat)
      (live : NumSet) (e : CrepExpHOL 64) :
      let compiled := compileExpHOLExact context tmp live e
      ∃ cost, loopExpressionCodesWork compiled.1 = some cost ∧
        cost + loopNativeValue compiled.2.1 ≤ loopNodePrice e := by
    cases e with
    | const value | var value | loadGlob value =>
      exact ⟨0, by simp [compileExpHOLExact, loopExpressionCodesWork], by
        simp [compileExpHOLExact, loopNativeValue, loopNodePrice]⟩
    | baseAddr | topAddr =>
      exact ⟨0, by simp [compileExpHOLExact, loopExpressionCodesWork], by
        simp [compileExpHOLExact, loopNativeValue, loopNodePrice]⟩
    | load address | load32 address | loadByte address =>
      rcases hc : compileExpHOLExact context tmp live address with ⟨code, value, next, out⟩
      obtain ⟨cost, supported, bound⟩ := crep_to_loop_price_work context tmp live address
      rw [hc] at supported bound
      all_goals simp only [] at supported bound
      all_goals first
        | (refine ⟨cost, ?_, ?_⟩
           · simpa only [compileExpHOLExact, hc] using supported
           · simp only [compileExpHOLExact, hc, loopNativeValue, loopNodePrice]; omega)
        | (refine ⟨cost + loopNativeValue value + 35, ?_, ?_⟩
           · simp [compileExpHOLExact, hc, loopExpressionCodesWork_append,
               loopExpressionCodesWork, loopExpressionCodeWork, supported, Nat.add_assoc]
           · simp only [compileExpHOLExact, hc, loopNativeValue, loopNodePrice]; omega)
    | shift operator left right | cmp operator left right =>
      rcases hl : compileExpHOLExact context tmp live left with ⟨lc, lv, ln, ll⟩
      rcases hr : compileExpHOLExact context ln ll right with ⟨rc, rv, rn, rl⟩
      obtain ⟨a, ha, ba⟩ := crep_to_loop_price_work context tmp live left
      obtain ⟨b, hb, bb⟩ := crep_to_loop_price_work context ln ll right
      rw [hl] at ha ba
      rw [hr] at hb bb
      all_goals simp only [] at ha ba hb bb
      all_goals first
        | (refine ⟨a + b, ?_, ?_⟩
           · simp [compileExpHOLExact, hl, hr, loopExpressionCodesWork_append, ha, hb]
           · simp only [compileExpHOLExact, hl, hr, loopNativeValue, loopNodePrice]; omega)
        | (refine ⟨a + b + loopNativeValue lv + loopNativeValue rv + 56, ?_, ?_⟩
           · simpa only [compileExpHOLExact, hl, hr] using
               comparison_materializer_work operator lc rc lv rv (rn+1) (rn+2) rl a b ha hb
           · simp only [compileExpHOLExact, hl, hr, loopNativeValue, loopNodePrice]; omega)
    | op operator args =>
      rcases hc : compileExpsHOLExact context tmp live args with ⟨code, values, next, out⟩
      obtain ⟨cost, supported, bound⟩ := crep_to_loop_price_list_work context tmp live args
      have len := price_compileExps_length context args tmp live
      rw [hc] at supported bound len
      simp only [] at len
      refine ⟨cost, ?_, ?_⟩
      · simpa only [compileExpHOLExact, hc] using supported
      · simp only [compileExpHOLExact, hc, loopNativeValue, loopNodePrice]
        simp only [] at bound
        omega
    | crepOp operator args =>
      rcases hc : compileExpsHOLExact context tmp live args with ⟨code, values, next, out⟩
      obtain ⟨cost, supported, bound⟩ := crep_to_loop_price_list_work context tmp live args
      rw [hc] at supported bound
      simp only [] at supported bound
      obtain ⟨assignCost, assignSupported, assignBound⟩ :=
        assignment_list_work (List.range values.length) values next
      cases operator
      simp only [compileExpHOLExact, hc, compileCrepopHOLExact]
      split <;> refine ⟨cost + assignCost + 43, ?_, ?_⟩
      all_goals simp [loopExpressionCodesWork_append, supported, assignSupported,
        loopExpressionCodesWork, loopExpressionCodeWork, loopNativeValue, loopNodePrice,
        Nat.add_assoc] <;> omega
  termination_by sizeOf e

  theorem crep_to_loop_price_list_work (context : CrepToLoopContextExact) (tmp : Nat)
      (live : NumSet) (es : List (CrepExpHOL 64)) :
      let compiled := compileExpsHOLExact context tmp live es
      ∃ cost, loopExpressionCodesWork compiled.1 = some cost ∧
        cost + loopNativeValues compiled.2.1 ≤ loopPriceList es := by
    cases es with
    | nil => exact ⟨0, by simp [compileExpsHOLExact, loopExpressionCodesWork],
        by simp [compileExpsHOLExact, loopNativeValues, loopPriceList]⟩
    | cons head tail =>
      rcases hh : compileExpHOLExact context tmp live head with ⟨hc, hv, hn, hl⟩
      rcases ht : compileExpsHOLExact context hn hl tail with ⟨tc, tv, tn, tl⟩
      obtain ⟨a, ha, ba⟩ := crep_to_loop_price_work context tmp live head
      obtain ⟨b, hb, bb⟩ := crep_to_loop_price_list_work context hn hl tail
      rw [hh] at ha ba
      rw [ht] at hb bb
      simp only [] at ha ba hb bb
      refine ⟨a + b, ?_, ?_⟩
      · simp [compileExpsHOLExact, hh, ht, loopExpressionCodesWork_append, ha, hb]
      · simp only [compileExpsHOLExact, hh, ht, loopNativeValues, loopPriceList, List.length_cons]
        omega
  termination_by sizeOf es
end

mutual
  /-- The native price never exceeds the coarse native ceiling. -/
  theorem loopNodePrice_le : ∀ e : CrepExpHOL 64, loopNodePrice e + 28 ≤ 160 * crepNodeWork e
    | .const _ | .var _ | .loadGlob _ | .baseAddr | .topAddr => by
      simp only [loopNodePrice, crepNodeWork]; omega
    | .load a | .load32 a | .loadByte a => by
      have := loopNodePrice_le a; simp only [loopNodePrice, crepNodeWork]; omega
    | .op _ args | .crepOp _ args => by
      have := loopPriceList_le args; simp only [loopNodePrice, crepNodeWork]; omega
    | .shift _ l r | .cmp _ l r => by
      have := loopNodePrice_le l; have := loopNodePrice_le r
      simp only [loopNodePrice, crepNodeWork]; omega
  termination_by e => sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  theorem loopPriceList_le : ∀ es : List (CrepExpHOL 64), loopPriceList es + 28 * es.length ≤ 160 * crepListWork es
    | [] => by simp [loopPriceList, crepListWork]
    | e :: es => by
      have := loopNodePrice_le e; have := loopPriceList_le es
      simp only [loopPriceList, crepListWork, List.length_cons]; omega
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

theorem loopNodePrice_pos : ∀ e : CrepExpHOL 64, 2 ≤ loopNodePrice e
  | .const _ | .var _ | .loadGlob _ | .baseAddr | .topAddr => by simp only [loopNodePrice]; omega
  | .load a | .load32 a | .loadByte a => by have := loopNodePrice_pos a; simp only [loopNodePrice]; omega
  | .op _ args | .crepOp _ args => by simp only [loopNodePrice]; omega
  | .shift _ l r | .cmp _ l r => by
    have := loopNodePrice_pos l; have := loopNodePrice_pos r
    simp only [loopNodePrice]; omega
termination_by e => sizeOf e

theorem loopPriceList_ge_length : ∀ es : List (CrepExpHOL 64), es.length ≤ loopPriceList es
  | [] => by simp [loopPriceList]
  | e :: es => by
    have := loopPriceList_ge_length es
    have := loopNodePrice_pos e
    simp only [loopPriceList, List.length_cons]; omega

/-- Sharp Crep price of an expression list: each expression's native price
plus one argument move (39). -/
def sharpCrepList (es : List (CrepExpHOL 64)) : Nat := loopPriceList es + 39 * es.length

#print axioms crep_to_loop_price_work
#print axioms loopNodePrice_le
end InitECandidate.Runtime.FineCost
