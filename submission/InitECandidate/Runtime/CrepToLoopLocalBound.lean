import InitECandidate.Runtime.LoopExpressionWork
import InitECandidate.Runtime.PanLoweringAllowance
namespace InitECandidate.Runtime.FineCost
open Flapjack

theorem assignment_list_work (offsets : List Nat) (values : List (HolLoopExp 64)) (base : Nat) :
    ∃ cost, loopExpressionCodesWork (offsets.zipWith
      (fun offset value => HolLoopProg.assign (base + offset) value) values) = some cost ∧
      cost ≤ loopNativeValues values := by
  induction offsets generalizing values with
  | nil => exact ⟨0, by simp [List.zipWith, loopExpressionCodesWork], by omega⟩
  | cons offset tail ih =>
    cases values with
    | nil => exact ⟨0, by simp [List.zipWith, loopExpressionCodesWork], by simp [loopNativeValues]⟩
    | cons value rest =>
      obtain ⟨cost, supported, bound⟩ := ih rest
      refine ⟨loopNativeValue value + cost, ?_, ?_⟩
      · simp [List.zipWith, loopExpressionCodesWork, loopExpressionCodeWork, supported]
      · simp only [loopNativeValues, List.length_cons]; omega

mutual
  /-- Local expansion, including residual expression work. The extra potential
  unit pays for argument materialization in enclosing variadic operations. -/
  theorem crep_to_loop_local_work (context : CrepToLoopContextExact) (tmp : Nat)
      (live : NumSet) (e : CrepExpHOL 64) :
      let compiled := compileExpHOLExact context tmp live e
      ∃ cost, loopExpressionCodesWork compiled.1 = some cost ∧
        cost + loopNativeValue compiled.2.1 + 39 ≤ 160 * crepNodeWork e := by
    cases e with
    | const value | var value | loadGlob value =>
      exact ⟨0, by simp [compileExpHOLExact, loopExpressionCodesWork], by
        simp [compileExpHOLExact, loopNativeValue, crepNodeWork]⟩
    | baseAddr | topAddr =>
      exact ⟨0, by simp [compileExpHOLExact, loopExpressionCodesWork], by
        simp [compileExpHOLExact, loopNativeValue, crepNodeWork]⟩
    | load address | load32 address | loadByte address =>
      rcases hc : compileExpHOLExact context tmp live address with ⟨code, value, next, out⟩
      obtain ⟨cost, supported, bound⟩ := crep_to_loop_local_work context tmp live address
      rw [hc] at supported bound
      all_goals simp only [] at supported bound
      all_goals first
        | (refine ⟨cost, ?_, ?_⟩
           · simpa only [compileExpHOLExact, hc] using supported
           · simp only [compileExpHOLExact, hc, loopNativeValue, crepNodeWork]; omega)
        | (refine ⟨cost + loopNativeValue value + 35, ?_, ?_⟩
           · simp [compileExpHOLExact, hc, loopExpressionCodesWork_append,
               loopExpressionCodesWork, loopExpressionCodeWork, supported, Nat.add_assoc]
           · simp only [compileExpHOLExact, hc, loopNativeValue, crepNodeWork]; omega)
    | shift operator left right | cmp operator left right =>
      rcases hl : compileExpHOLExact context tmp live left with ⟨lc, lv, ln, ll⟩
      rcases hr : compileExpHOLExact context ln ll right with ⟨rc, rv, rn, rl⟩
      obtain ⟨a, ha, ba⟩ := crep_to_loop_local_work context tmp live left
      obtain ⟨b, hb, bb⟩ := crep_to_loop_local_work context ln ll right
      rw [hl] at ha ba
      rw [hr] at hb bb
      all_goals simp only [] at ha ba hb bb
      all_goals first
        | (refine ⟨a + b, ?_, ?_⟩
           · simp [compileExpHOLExact, hl, hr, loopExpressionCodesWork_append, ha, hb]
           · simp only [compileExpHOLExact, hl, hr, loopNativeValue, crepNodeWork]; omega)
        | (refine ⟨a + b + loopNativeValue lv + loopNativeValue rv + 56, ?_, ?_⟩
           · simpa only [compileExpHOLExact, hl, hr] using
               comparison_materializer_work operator lc rc lv rv (rn+1) (rn+2) rl a b ha hb
           · simp only [compileExpHOLExact, hl, hr, loopNativeValue, crepNodeWork]; omega)
    | op operator args =>
      rcases hc : compileExpsHOLExact context tmp live args with ⟨code, values, next, out⟩
      obtain ⟨cost, supported, bound⟩ := crep_to_loop_list_work context tmp live args
      rw [hc] at supported bound
      refine ⟨cost, ?_, ?_⟩
      · simpa only [compileExpHOLExact, hc] using supported
      · simp only [compileExpHOLExact, hc, loopNativeValue, crepNodeWork]
        simp only [] at bound
        omega
    | crepOp operator args =>
      rcases hc : compileExpsHOLExact context tmp live args with ⟨code, values, next, out⟩
      obtain ⟨cost, supported, bound⟩ := crep_to_loop_list_work context tmp live args
      rw [hc] at supported bound
      simp only [] at supported bound
      obtain ⟨assignCost, assignSupported, assignBound⟩ :=
        assignment_list_work (List.range values.length) values next
      cases operator
      simp only [compileExpHOLExact, hc, compileCrepopHOLExact]
      split <;> refine ⟨cost + assignCost + 43, ?_, ?_⟩
      all_goals simp [loopExpressionCodesWork_append, supported, assignSupported,
        loopExpressionCodesWork, loopExpressionCodeWork, loopNativeValue, crepNodeWork,
        Nat.add_assoc] <;> omega
  termination_by sizeOf e

  theorem crep_to_loop_list_work (context : CrepToLoopContextExact) (tmp : Nat)
      (live : NumSet) (es : List (CrepExpHOL 64)) :
      let compiled := compileExpsHOLExact context tmp live es
      ∃ cost, loopExpressionCodesWork compiled.1 = some cost ∧
        cost + loopNativeValues compiled.2.1 + 39 * compiled.2.1.length ≤ 160 * crepListWork es := by
    cases es with
    | nil => exact ⟨0, by simp [compileExpsHOLExact, loopExpressionCodesWork], by simp [compileExpsHOLExact, loopNativeValues, crepListWork]⟩
    | cons head tail =>
      rcases hh : compileExpHOLExact context tmp live head with ⟨hc, hv, hn, hl⟩
      rcases ht : compileExpsHOLExact context hn hl tail with ⟨tc, tv, tn, tl⟩
      obtain ⟨a, ha, ba⟩ := crep_to_loop_local_work context tmp live head
      obtain ⟨b, hb, bb⟩ := crep_to_loop_list_work context hn hl tail
      rw [hh] at ha ba
      rw [ht] at hb bb
      refine ⟨a + b, ?_, ?_⟩
      · simp [compileExpsHOLExact, hh, ht, loopExpressionCodesWork_append, ha, hb]
      · simp only [compileExpsHOLExact, hh, ht, loopNativeValues, List.length_cons, crepListWork]
        simp only [] at ba bb
        omega
  termination_by sizeOf es
end

/-- Source expression flattening and scalar expression lowering compose with
coefficient 160. Contexts remain explicit because preprocessing and whole-
program layout still need their separate correctness/cost connections. -/
theorem pan_to_loop_expression_work
    (panContext : PanToCrepContextExact 64) (loopContext : CrepToLoopContextExact)
    (tmp : Nat) (live : NumSet) (expression : Pancake.PanLang.ExpHOL 64) :
    let expressions := (compileExpExactHOLW panContext expression).1
    let compiled := compileExpsHOLExact loopContext tmp live expressions
    ∃ cost, loopExpressionCodesWork compiled.1 = some cost ∧
      cost + loopNativeValues compiled.2.1 + 39 * compiled.2.1.length ≤
        160 * panLoweringAllowance panContext expression := by
  obtain ⟨cost, supported, bound⟩ := crep_to_loop_list_work loopContext tmp live
    (compileExpExactHOLW panContext expression).1
  refine ⟨cost, supported, Nat.le_trans bound ?_⟩
  exact Nat.mul_le_mul_left 160 (pan_lowering_work_bound panContext expression)

#print axioms pan_to_loop_expression_work

#print axioms crep_to_loop_local_work
#print axioms crep_to_loop_list_work
end InitECandidate.Runtime.FineCost
