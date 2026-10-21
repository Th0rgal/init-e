import InitECandidate.Runtime.LoopLeafSelPrice
import InitECandidate.Runtime.LoopExpressionWork
import InitECandidate.Runtime.SourceCostLoopPrice
namespace InitECandidate.Runtime.FineCost
open Flapjack

/-! Selector-derived price of a Crep expression: the selector-priced work of
the Loop code `crep_to_loop$compile_exp` generates for it, plus the selector
price of its residual Loop value. Context-free. -/

/-- Selector allowance of a list of expression-generated Loop statements. -/
def selCodesWork : List (HolLoopProg 64) → Option Nat
  | [] => some 0
  | p :: ps => do
      let a ← selCodeWork p
      let b ← selCodesWork ps
      pure (a + b)

theorem selCodesWork_append : ∀ (l r : List (HolLoopProg 64)),
    selCodesWork (l ++ r) = (do
      let a ← selCodesWork l
      let b ← selCodesWork r
      pure (a + b))
  | [], r => by simp [selCodesWork]
  | p :: l, r => by
    simp only [List.cons_append, selCodesWork, selCodesWork_append l r]
    cases selCodeWork p <;> cases selCodesWork l <;> cases selCodesWork r <;> simp [Nat.add_assoc]

mutual
/-- Selector price of a Crep expression. -/
def selNodePrice : CrepExpHOL 64 → Nat
  | .const _ | .var _ | .loadGlob _ | .baseAddr => 24
  | .topAddr => 124
  | .load a => selNodePrice a + 24
  | .load32 a | .loadByte a => selNodePrice a + 48
  | .op _ args => selPriceList args + 24 * (args.length - 1) + 24 * (1 - args.length)
  | .crepOp _ args => selPriceList args + 51
  | .shift _ l r => selNodePrice l + selNodePrice r + 28
  | .cmp _ l r => selNodePrice l + selNodePrice r + 85
termination_by e => sizeOf e
decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

/-- Sum of `selNodePrice` over a list. -/
def selPriceList : List (CrepExpHOL 64) → Nat
  | [] => 0
  | e :: es => selNodePrice e + selPriceList es
termination_by es => sizeOf es
decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

theorem sel_assignment_list (offsets : List Nat) (values : List (HolLoopExp 64)) (base : Nat) :
    ∃ cost, selCodesWork (offsets.zipWith
      (fun offset value => HolLoopProg.assign (base + offset) value) values) = some cost ∧
      cost ≤ fLs values := by
  induction offsets generalizing values with
  | nil => exact ⟨0, by simp [List.zipWith, selCodesWork], by omega⟩
  | cons offset tail ih =>
    cases values with
    | nil => exact ⟨0, by simp [List.zipWith, selCodesWork], by simp [fLs]⟩
    | cons value rest =>
      obtain ⟨cost, supported, bound⟩ := ih rest
      refine ⟨fL value + cost, ?_, ?_⟩
      · simp [List.zipWith, selCodesWork, selCodeWork, supported]
      · simp only [fLs]; omega

theorem sel_compileExps_length (context : CrepToLoopContextExact) :
    ∀ (es : List (CrepExpHOL 64)) (tmp : Nat) (live : NumSet),
      (compileExpsHOLExact context tmp live es).2.1.length = es.length :=
  price_compileExps_length context

mutual
  theorem crep_to_loop_sel_work (context : CrepToLoopContextExact) (tmp : Nat)
      (live : NumSet) (e : CrepExpHOL 64) :
      let compiled := compileExpHOLExact context tmp live e
      ∃ cost, selCodesWork compiled.1 = some cost ∧ cost + fL compiled.2.1 ≤ selNodePrice e := by
    cases e with
    | const value | var value | loadGlob value =>
      exact ⟨0, by simp [compileExpHOLExact, selCodesWork], by simp [compileExpHOLExact, fL, selNodePrice]⟩
    | baseAddr | topAddr =>
      exact ⟨0, by simp [compileExpHOLExact, selCodesWork], by simp [compileExpHOLExact, fL, selNodePrice]⟩
    | load address =>
      rcases hc : compileExpHOLExact context tmp live address with ⟨code, value, next, out⟩
      obtain ⟨cost, supported, bound⟩ := crep_to_loop_sel_work context tmp live address
      rw [hc] at supported bound
      simp only [] at supported bound
      refine ⟨cost, by simpa only [compileExpHOLExact, hc] using supported, ?_⟩
      simp only [compileExpHOLExact, hc, fL, selNodePrice]; omega
    | load32 address | loadByte address =>
      rcases hc : compileExpHOLExact context tmp live address with ⟨code, value, next, out⟩
      obtain ⟨cost, supported, bound⟩ := crep_to_loop_sel_work context tmp live address
      rw [hc] at supported bound
      simp only [] at supported bound
      all_goals
        refine ⟨cost + fL value + 24, ?_, ?_⟩
        · simp [compileExpHOLExact, hc, selCodesWork_append, selCodesWork, selCodeWork, supported, Nat.add_assoc]
        · simp only [compileExpHOLExact, hc, fL, selNodePrice]; omega
    | shift operator left right | cmp operator left right =>
      rcases hl : compileExpHOLExact context tmp live left with ⟨lc, lv, ln, ll⟩
      rcases hr : compileExpHOLExact context ln ll right with ⟨rc, rv, rn, rl⟩
      obtain ⟨a, ha, ba⟩ := crep_to_loop_sel_work context tmp live left
      obtain ⟨b, hb, bb⟩ := crep_to_loop_sel_work context ln ll right
      rw [hl] at ha ba
      rw [hr] at hb bb
      all_goals simp only [] at ha ba hb bb
      all_goals first
        | (refine ⟨a + b, ?_, ?_⟩
           · simp [compileExpHOLExact, hl, hr, selCodesWork_append, ha, hb]
           · simp only [compileExpHOLExact, hl, hr, fL, selNodePrice]; omega)
        | (refine ⟨a + b + fL lv + fL rv + 61, ?_, ?_⟩
           · simp [compileExpHOLExact, hl, hr, progIfHOLExact, selCodesWork_append, selCodesWork, selCodeWork,
               ha, hb, fL]
             omega
           · simp only [compileExpHOLExact, hl, hr, fL, selNodePrice]; omega)
    | op operator args =>
      rcases hc : compileExpsHOLExact context tmp live args with ⟨code, values, next, out⟩
      obtain ⟨cost, supported, bound⟩ := crep_to_loop_sel_list_work context tmp live args
      have len := sel_compileExps_length context args tmp live
      rw [hc] at supported bound len
      simp only [] at len supported bound
      refine ⟨cost, by simpa only [compileExpHOLExact, hc] using supported, ?_⟩
      simp only [compileExpHOLExact, hc, fL, selNodePrice, len]
      omega
    | crepOp operator args =>
      rcases hc : compileExpsHOLExact context tmp live args with ⟨code, values, next, out⟩
      obtain ⟨cost, supported, bound⟩ := crep_to_loop_sel_list_work context tmp live args
      rw [hc] at supported bound
      simp only [] at supported bound
      obtain ⟨assignCost, assignSupported, assignBound⟩ :=
        sel_assignment_list (List.range values.length) values next
      cases operator
      simp only [compileExpHOLExact, hc, compileCrepopHOLExact]
      split <;> refine ⟨cost + assignCost + 27, ?_, ?_⟩
      all_goals simp [selCodesWork_append, supported, assignSupported, selCodesWork, selCodeWork, fL,
        selNodePrice, Nat.add_assoc] <;> omega
  termination_by sizeOf e

  theorem crep_to_loop_sel_list_work (context : CrepToLoopContextExact) (tmp : Nat)
      (live : NumSet) (es : List (CrepExpHOL 64)) :
      let compiled := compileExpsHOLExact context tmp live es
      ∃ cost, selCodesWork compiled.1 = some cost ∧ cost + fLs compiled.2.1 ≤ selPriceList es := by
    cases es with
    | nil => exact ⟨0, by simp [compileExpsHOLExact, selCodesWork], by simp [compileExpsHOLExact, fLs, selPriceList]⟩
    | cons head tail =>
      rcases hh : compileExpHOLExact context tmp live head with ⟨hc, hv, hn, hl⟩
      rcases ht : compileExpsHOLExact context hn hl tail with ⟨tc, tv, tn, tl⟩
      obtain ⟨a, ha, ba⟩ := crep_to_loop_sel_work context tmp live head
      obtain ⟨b, hb, bb⟩ := crep_to_loop_sel_list_work context hn hl tail
      rw [hh] at ha ba
      rw [ht] at hb bb
      simp only [] at ha ba hb bb
      refine ⟨a + b, ?_, ?_⟩
      · simp [compileExpsHOLExact, hh, ht, selCodesWork_append, ha, hb]
      · simp only [compileExpsHOLExact, hh, ht, fLs, selPriceList]
        omega
  termination_by sizeOf es
end

#print axioms crep_to_loop_sel_work
end InitECandidate.Runtime.FineCost
