import InitECandidate.Runtime.CrepToLoopLocalBound
import Flapjack.Pancake.Semantics.LoopProps.NestedSeqExact
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

def loopWorkAtomic : HolLoopProg 64 → Bool
  | .skip | .assign _ _ | .arith _ | .load32 _ _ | .loadByte _ _ => true
  | _ => false

/-- Executed Loop prefixes with conservative expression-local charges.
Branches expose only the selected child. Calls/loops are not opaque atoms. -/
inductive LoopWorkRun {F : Type} : LoopSemStateFiniteExact 64 F → HolLoopProg 64 →
    (Option (LoopResultExact 64) × LoopSemStateFiniteExact 64 F) → Nat → Prop where
  | atom {s p output cost} (atomic : loopWorkAtomic p = true)
      (localCost : loopExpressionCodeWork p = some cost)
      (run : evaluate p s = output) : LoopWorkRun s p output cost
  | seqNext {s first second middle output a b}
      (one : LoopWorkRun s first (none, middle) a)
      (two : LoopWorkRun middle second output b) :
      LoopWorkRun s (.seq first second) output (a+b)
  | seqStop {s first second result post a} (terminal : result ≠ none)
      (one : LoopWorkRun s first (result, post) a) :
      LoopWorkRun s (.seq first second) (result, post) a
  | iteYes {s operator register right yes no live x y output cost}
      (lhs : sptLookup register s.locals = some (.word x))
      (rhs : LoopSemStateFiniteExact.getVarImm right s = some (.word y))
      (chosen : Compiler.Encoders.Asm.wordCmpHOL operator x y = true)
      (child : LoopWorkRun s yes output cost) :
      LoopWorkRun s (.ite operator register right yes no live) (cutRes live output) (2+cost)
  | iteNo {s operator register right yes no live x y output cost}
      (lhs : sptLookup register s.locals = some (.word x))
      (rhs : LoopSemStateFiniteExact.getVarImm right s = some (.word y))
      (chosen : Compiler.Encoders.Asm.wordCmpHOL operator x y = false)
      (child : LoopWorkRun s no output cost) :
      LoopWorkRun s (.ite operator register right yes no live) (cutRes live output) (2+cost)

  | iteNoWords {s operator register right yes no live}
      (invalid : ¬ ∃ x y, sptLookup register s.locals = some (.word x) ∧
        LoopSemStateFiniteExact.getVarImm right s = some (.word y)) :
      LoopWorkRun s (.ite operator register right yes no live) (some .error, s) 1

theorem LoopWorkRun.sound {F : Type} {s : LoopSemStateFiniteExact 64 F}
    {p : HolLoopProg 64} {output cost} (run : LoopWorkRun s p output cost) :
    evaluate p s = output := by
  induction run with
  | atom atomic localCost run => exact run
  | seqNext one two ihOne ihTwo => rw [evaluate_seq, ihOne]; exact ihTwo
  | seqStop terminal one ih => rw [evaluate_seq, ih]; split <;> simp_all
  | iteYes lhs rhs chosen child ih => rw [evaluate.eq_13, lhs, rhs]; simp [chosen, ih]
  | iteNo lhs rhs chosen child ih => rw [evaluate.eq_13, lhs, rhs]; simp [chosen, ih]
  | iteNoWords invalid =>
    rw [evaluate.eq_13]
    split
    · rename_i x y hx hy
      exact False.elim (invalid ⟨x, y, hx, hy⟩)
    · rfl

/-- The generated-code allowance bounds the work on the actual selected path. -/
theorem LoopWorkRun.bounded {F : Type} {s : LoopSemStateFiniteExact 64 F}
    {p : HolLoopProg 64} {output cost} (run : LoopWorkRun s p output cost)
    (ceiling : Nat) (supported : loopExpressionCodeWork p = some ceiling) : cost ≤ ceiling := by
  induction run generalizing ceiling with
  | atom atomic localCost run => rw [localCost] at supported; cases supported; omega
  | @seqNext s first second middle output a b one two ihOne ihTwo =>
    simp only [loopExpressionCodeWork] at supported
    cases ha : loopExpressionCodeWork first <;> cases hb : loopExpressionCodeWork second <;>
      simp_all
    omega
  | @seqStop s first second result post a terminal one ih =>
    simp only [loopExpressionCodeWork] at supported
    cases ha : loopExpressionCodeWork first <;> cases hb : loopExpressionCodeWork second <;>
      simp_all
    omega
  | @iteYes s operator register right yes no live x y output cost lhs rhs chosen child ih =>
    simp only [loopExpressionCodeWork] at supported
    cases ha : loopExpressionCodeWork yes <;> cases hb : loopExpressionCodeWork no <;>
      simp_all
    omega
  | @iteNo s operator register right yes no live x y output cost lhs rhs chosen child ih =>
    simp only [loopExpressionCodeWork] at supported
    cases ha : loopExpressionCodeWork yes <;> cases hb : loopExpressionCodeWork no <;>
      simp_all
    omega
  | @iteNoWords s operator register right yes no live invalid =>
    simp only [loopExpressionCodeWork] at supported
    cases ha : loopExpressionCodeWork yes <;> cases hb : loopExpressionCodeWork no <;>
      simp_all
    omega

/-- Every supported expression-code program has an exact executed trace with
work below its static allowance, including early termination and guard errors. -/
theorem loop_work_trace_complete {F : Type} (p : HolLoopProg 64)
    (s : LoopSemStateFiniteExact 64 F) (ceiling : Nat)
    (supported : loopExpressionCodeWork p = some ceiling) :
    ∃ cost, LoopWorkRun s p (evaluate p s) cost ∧ cost ≤ ceiling := by
  classical
  cases p with
  | skip | assign _ _ | arith _ | load32 _ _ | loadByte _ _ =>
    exact ⟨ceiling, .atom rfl supported rfl, Nat.le_refl _⟩
  | seq first second =>
    cases ha : loopExpressionCodeWork first with
    | none => simp [loopExpressionCodeWork, ha] at supported
    | some a =>
      cases hb : loopExpressionCodeWork second with
      | none => simp [loopExpressionCodeWork, ha, hb] at supported
      | some b =>
        obtain ⟨firstCost, firstRun, firstBound⟩ := loop_work_trace_complete first s a ha
        rcases he : evaluate first s with ⟨result, middle⟩
        rw [he] at firstRun
        cases result with
        | none =>
          obtain ⟨secondCost, secondRun, secondBound⟩ := loop_work_trace_complete second middle b hb
          refine ⟨firstCost + secondCost, ?_, ?_⟩
          · simpa only [evaluate_seq, he] using LoopWorkRun.seqNext firstRun secondRun
          · simp [loopExpressionCodeWork, ha, hb] at supported; omega
        | some result =>
          refine ⟨firstCost, ?_, ?_⟩
          · simpa only [evaluate_seq, he] using
              (LoopWorkRun.seqStop (second := second) (by simp) firstRun)
          · simp [loopExpressionCodeWork, ha, hb] at supported; omega
  | ite operator register right yes no live =>
    cases ha : loopExpressionCodeWork yes with
    | none => simp [loopExpressionCodeWork, ha] at supported
    | some a =>
      cases hb : loopExpressionCodeWork no with
      | none => simp [loopExpressionCodeWork, ha, hb] at supported
      | some b =>
        by_cases words : ∃ x y, sptLookup register s.locals = some (.word x) ∧
            LoopSemStateFiniteExact.getVarImm right s = some (.word y)
        · obtain ⟨x, y, lhs, rhs⟩ := words
          cases chosen : Compiler.Encoders.Asm.wordCmpHOL operator x y with
          | true =>
            obtain ⟨cost, run, bound⟩ := loop_work_trace_complete yes s a ha
            refine ⟨2 + cost, ?_, ?_⟩
            · simpa [evaluate.eq_13, lhs, rhs, chosen] using
                (LoopWorkRun.iteYes (no := no) (live := live) lhs rhs chosen run)
            · simp [loopExpressionCodeWork, ha, hb] at supported; omega
          | false =>
            obtain ⟨cost, run, bound⟩ := loop_work_trace_complete no s b hb
            refine ⟨2 + cost, ?_, ?_⟩
            · simpa [evaluate.eq_13, lhs, rhs, chosen] using
                (LoopWorkRun.iteNo (yes := yes) (live := live) lhs rhs chosen run)
            · simp [loopExpressionCodeWork, ha, hb] at supported; omega
        · have run := LoopWorkRun.iteNoWords (operator := operator) (yes := yes)
            (no := no) (live := live) words
          refine ⟨1, ?_, ?_⟩
          · rw [run.sound]; exact run
          · simp [loopExpressionCodeWork, ha, hb] at supported; omega
  | _ => simp [loopExpressionCodeWork] at supported
termination_by sizeOf p

#print axioms loop_work_trace_complete

theorem loop_nested_code_work (code : List (HolLoopProg 64)) :
    loopExpressionCodeWork (loopNestedSeqHOL code) = loopExpressionCodesWork code := by
  induction code with
  | nil => simp [loopNestedSeqHOL, loopExpressionCodeWork, loopExpressionCodesWork]
  | cons head tail ih =>
    simp only [loopNestedSeqHOL, loopExpressionCodeWork, loopExpressionCodesWork, ih]

/-- The coefficient-six expansion bound now bounds a real evaluator trace,
including the residual values still to be consumed by its surrounding statement. -/
theorem compiled_pan_expression_trace {F : Type}
    (panContext : PanToCrepContextExact 64) (loopContext : CrepToLoopContextExact)
    (tmp : Nat) (live : NumSet) (expression : Pancake.PanLang.ExpHOL 64)
    (state : LoopSemStateFiniteExact 64 F) :
    let expressions := (compileExpExactHOLW panContext expression).1
    let compiled := compileExpsHOLExact loopContext tmp live expressions
    ∃ cost, LoopWorkRun state (loopNestedSeqHOL compiled.1)
        (evaluate (loopNestedSeqHOL compiled.1) state) cost ∧
      cost + loopValuesWork compiled.2.1 + compiled.2.1.length ≤
        6 * panLoweringAllowance panContext expression := by
  obtain ⟨allowance, supported, bound⟩ :=
    pan_to_loop_expression_work panContext loopContext tmp live expression
  rw [← loop_nested_code_work] at supported
  obtain ⟨cost, trace, small⟩ := loop_work_trace_complete _ state allowance supported
  exact ⟨cost, trace, by omega⟩

#print axioms compiled_pan_expression_trace

#print axioms LoopWorkRun.sound
#print axioms LoopWorkRun.bounded
end InitECandidate.Runtime.FineCost
