import Flapjack.Compiler.Backend.WordToWord.Compile
import Flapjack.Compiler.Backend.WordAlloc.SSACcTrans
import InitECandidate.Runtime.WordPathWorkControl
import InitECandidate.Runtime.WordSelectionStraightLine
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.WordAlloc Flapjack.WordSemStateFiniteExact
open InitECandidate.Runtime.WordToStack

/-!
# Word-to-Word executed-work model for the optimizer/SSA/allocation stage

The source cost model (`PanStatementWork`/`PanCostTotal`) charges one event per
executed statement and expression plus size-sensitive memory/copy/frame events.
This module starts the corresponding local Word-stage transfer.  `wordNodeCost`
is the syntactic envelope of one function body: one unit per executed
instruction or move word, one per control node and one per parallel-move pair.
It intentionally contains no whole-program AST/ROM maximum and no bitmap or
code-table size.  `wordPathWork` (the actual selected-path budget already used
by `WordSelectedPathCost`) is bounded by this envelope on straight-line
fragments, and later modules transport the envelope through SSA, three-to-two
registers and register allocation, adding only the moves those passes insert.
-/

/-- Local syntactic work of one Word function body.  A parallel move costs one
unit per moved word; sequences, conditionals, loops and call handlers cost one
control unit plus their synthetic children.  Calls do not charge the callee
body here: callee work belongs to the separate function-table composition. -/
def wordNodeCost : WordLangProgHOL (BitVec 64) → Nat
  | .skip => 1
  | .move _ moves => 1 + moves.length
  | .inst _ => 1
  | .assign _ _ => 1
  | .get _ _ => 1
  | .set _ _ => 1
  | .store _ _ => 1
  | .mustTerminate body => 1 + wordNodeCost body
  | .call none _ _ handler =>
      1 + match handler with
          | none => 0
          | some (_, code, _, _) => wordNodeCost code
  | .call (some (_, _, returnCode, _, _)) _ _ handler =>
      1 + wordNodeCost returnCode +
        match handler with
        | none => 0
        | some (_, code, _, _) => wordNodeCost code
  | .seq first second => 1 + wordNodeCost first + wordNodeCost second
  | .ite _ _ _ thenBranch elseBranch =>
      1 + wordNodeCost thenBranch + wordNodeCost elseBranch
  | .loop _ body _ => 1 + wordNodeCost body
  | .alloc _ _ => 1
  | .storeConsts _ _ _ _ _ => 1
  | .raise _ => 1
  | .return _ _ => 1
  | .break _ => 1
  | .continue _ => 1
  | .tick => 1
  | .opCurrHeap _ _ _ => 1
  | .locValue _ _ => 1
  | .install _ _ _ _ _ => 1
  | .codeBufferWrite _ _ => 1
  | .dataBufferWrite _ _ => 1
  | .ffi _ _ _ _ _ _ => 1
  | .shareInst _ _ _ => 1
termination_by p => sizeOf p

/-- Move words actually present in a program fragment.  These are the words a
parallel move must execute, not a whole-program maximum. -/
def wordMoveWords : WordLangProgHOL (BitVec 64) → Nat
  | .move _ moves => moves.length
  | .seq first second => wordMoveWords first + wordMoveWords second
  | .mustTerminate body => wordMoveWords body
  | .ite _ _ _ thenBranch elseBranch =>
      wordMoveWords thenBranch + wordMoveWords elseBranch
  | .loop _ body _ => wordMoveWords body
  | .call none _ _ handler =>
      match handler with
      | none => 0
      | some (_, code, _, _) => wordMoveWords code
  | .call (some (_, _, returnCode, _, _)) _ _ handler =>
      wordMoveWords returnCode +
        match handler with
        | none => 0
        | some (_, code, _, _) => wordMoveWords code
  | _ => 0
termination_by p => sizeOf p

/-- On the straight-line selector grammar the executed selected-path budget is
bounded by the syntactic envelope.  This is the fragment-level bridge from the
existing `WordSelectedPathCost` unit to the transfer proved below. -/
theorem wordPathWork_le_nodeCost {C F : Type}
    (p : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (supported : selectionStraightLine p = true) :
    wordPathWork p source ≤ wordNodeCost p := by
  cases p <;> simp only [selectionStraightLine, Bool.and_eq_true, decide_eq_true_eq] at supported
  all_goals try contradiction
  all_goals try (simp only [wordPathWork, wordNodeCost]; omega)
  case seq first second =>
    have firstBound := wordPathWork_le_nodeCost first source supported.1
    rw [wordPathWork_seq]
    simp only [wordNodeCost]
    cases run : evaluate first source with
    | mk result middle =>
      cases result with
      | none =>
        have secondBound := wordPathWork_le_nodeCost second middle supported.2
        dsimp only
        omega
      | some value => dsimp only; omega
termination_by sizeOf p
decreasing_by all_goals (subst_vars; simp_wf; try omega)

#print axioms wordPathWork_le_nodeCost
end InitECandidate.Runtime.FineCost
