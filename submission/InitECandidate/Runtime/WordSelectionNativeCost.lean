import InitECandidate.Runtime.WordNativeMoveCost
import InitECandidate.Runtime.WordSelectionStraightLine
import InitECandidate.Runtime.StackPathWorkCorrect
import Flapjack.Compiler.Backend.WordToStack.NativeCompile
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordToStackRegFormat
open Flapjack.Compiler.Encoders.Asm

/-- The straight-line selector grammar lowers with at most four Stack leaves
per Word leaf, including all reloads and spills for any frame assignment. -/
theorem selection_native_fragment (config : AsmConfigExact 64) (perf : Bool)
    (p : WordLangProgHOL (BitVec 64)) (bs : AppList (BitVec 64) × Nat)
    (kf : Nat × Nat × Nat) (supported : selectionStraightLine p = true) :
    stackStraightLine (compNative config perf p bs kf).1 = true ∧
    stackLeaves (compNative config perf p bs kf).1 ≤ 4 * selectionLeaves p := by
  cases p <;> simp only [selectionStraightLine, Bool.and_eq_true, decide_eq_true_eq] at supported
  all_goals try contradiction
  case skip => simp [compNative, stackStraightLine, stackLeaves, selectionLeaves]
  case inst instruction =>
    simpa only [compNative, selectionLeaves] using
      And.intro (native_instruction_straight (HolInst.ofWordLangInst instruction) kf)
        (native_instruction_leaves (HolInst.ofWordLangInst instruction) kf)
  case move priority moves =>
    cases moves with
    | nil => simp at supported
    | cons pair rest =>
      cases rest with
      | cons next tail => simp at supported
      | nil =>
        rcases pair with ⟨destination, source⟩
        simp only [compNative, selectionLeaves, List.length_cons, List.length_nil]
        refine ⟨native_singleton_move_straight destination source kf, ?_⟩
        exact Nat.le_trans (native_singleton_move_leaves destination source kf) (by omega)
  case get destination name =>
    constructor
    · simp only [compNative]
      apply native_write_straight
      intro n
      rfl
    · simp only [compNative, selectionLeaves]
      apply Nat.le_trans (native_write_leaves _ _ kf (by intro n; rfl))
      omega
  case opCurrHeap operator destination src =>
    constructor
    · simp only [compNative]
      apply native_load_straight
      apply native_write_straight
      intro n
      rfl
    · simp only [compNative, native_load_leaves, selectionLeaves]
      apply Nat.le_trans (Nat.add_le_add (first_register_load_count _ kf)
        (native_write_leaves _ _ kf (by intro n; rfl)))
      omega
  case seq first second =>
    have firstBound := selection_native_fragment config perf first bs kf supported.1
    have secondBound := selection_native_fragment config perf second
      (compNative config perf first bs kf).2 kf supported.2
    constructor
    · simpa only [compNative, stackStraightLine, Bool.and_eq_true] using
        And.intro firstBound.1 secondBound.1
    · simp only [compNative, stackLeaves, selectionLeaves]
      omega
termination_by sizeOf p

/-- Includes preprocessing, binary normalization and worst-case frame spills.
No whole-program frame-size or code-size multiplier appears. -/
theorem assignment_native_path_bound {C F : Type}
    (config : AsmConfigExact 64) (perf : Bool) (target temp : Nat)
    (expression : WordLangExpHOL (BitVec 64)) (bs : AppList (BitVec 64) × Nat)
    (kf : Nat × Nat × Nat) (source : StackSemStateFiniteExact 64 C F) :
    StackToLab.pathWork (compNative config perf
      (Flapjack.Compiler.Backend.WordInst.instSelect config temp (.assign target expression)) bs kf).1
      source ≤ 32 * wordExpressionWork expression := by
  let selected := Flapjack.Compiler.Backend.WordInst.instSelect config temp (.assign target expression)
  have grammar : selectionStraightLine selected = true := by
    simpa only [selected, Flapjack.Compiler.Backend.WordInst.instSelect] using
      raw_selection_straight_line config target temp
        (Flapjack.Compiler.Backend.WordInst.flattenExp
          (Flapjack.Compiler.Backend.WordInst.pullExp expression))
  have fragment := selection_native_fragment config perf selected bs kf grammar
  have pathBound := stack_straight_path_bound _ source fragment.1
  have leavesBound := assignment_selection_work_bound config target temp expression
  change selectionLeaves selected + 1 ≤ 2 * wordExpressionWork expression at leavesBound
  dsimp only [selected] at *
  omega

/-- Full original flattening simulation with the local expression budget.
This does not bypass Stack removal, allocation, or final native lowering. -/
theorem assignment_native_flatten_bound {C F : Type}
    (config : AsmConfigExact 64) (perf : Bool) (target temp : Nat)
    (expression : WordLangExpHOL (BitVec 64)) (bs : AppList (BitVec 64) × Nat)
    (kf : Nat × Nat × Nat) (source : StackSemStateFiniteExact 64 C F) :
    StackToLab.BoundedFlattenProp (compNative config perf
      (Flapjack.Compiler.Backend.WordInst.instSelect config temp (.assign target expression)) bs kf).1
      source (32 * wordExpressionWork expression) := by
  exact StackToLab.boundedFlattenProp_mono
    (assignment_native_path_bound config perf target temp expression bs kf source)
    (StackToLab.pathWork_correct _ source)

/-- Exact Loop-to-Word expression lowering preserves this local work unit. -/
theorem loop_assignment_native_path_bound {C F : Type}
    (config : AsmConfigExact 64) (perf : Bool) (context : Spt Nat) (target temp : Nat)
    (expression : HolLoopExp 64) (bs : AppList (BitVec 64) × Nat)
    (kf : Nat × Nat × Nat) (source : StackSemStateFiniteExact 64 C F) :
    StackToLab.pathWork (compNative config perf
      (Flapjack.Compiler.Backend.WordInst.instSelect config temp
        (.assign target (LoopToWord.compExpHOL context expression))) bs kf).1
      source ≤ 32 * loopValueWork expression := by
  simpa only [loop_to_word_expression_work] using
    assignment_native_path_bound config perf target temp
      (LoopToWord.compExpHOL context expression) bs kf source

#print axioms loop_assignment_native_path_bound
#print axioms assignment_native_path_bound
#print axioms assignment_native_flatten_bound
#print axioms selection_native_fragment
end InitECandidate.Runtime.FineCost
