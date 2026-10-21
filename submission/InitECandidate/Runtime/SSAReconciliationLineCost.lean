import InitECandidate.Runtime.WordLineCost
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAFixInconsistenciesCorrectLeft
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAFixInconsistenciesCorrectRight
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000
set_option pp.structureInstances false

/-- Exact local leaf prices of generated reconciliation fragments. Summing
these retains real pair lists, priorities, registers and fake constants. -/
def ssaReconciliationLeaf (price : WordLangProgHOL (BitVec 64) → Nat)
    (program : WordLangProgHOL (BitVec 64)) : Option Nat :=
  match program with
  | .skip | .move _ _ | .inst _ => some (price program)
  | _ => none

/-- Static sum for a reconciliation already certified as straight-line.
The compiler-shape theorem below discharges that certification. -/
def ssaReconciliationPrice (price : WordLangProgHOL (BitVec 64) → Nat)
    (program : WordLangProgHOL (BitVec 64)) : Nat :=
  (lineBound (ssaReconciliationLeaf price) program).getD 0

/-- Every actual fake-move output has a finite exact leaf sum. -/
theorem ssa_fake_moves_line (price : WordLangProgHOL (BitVec 64) → Nat)
    (prio : Option (Unit ⊕ Unit)) (names : List Nat) (left right : Spt Nat) (next : Nat) :
    ∃ l r,
      lineBound (ssaReconciliationLeaf price) (fakeMoves (width := 64) prio names left right next).1 = some l ∧
      lineBound (ssaReconciliationLeaf price) (fakeMoves (width := 64) prio names left right next).2.1 = some r := by
  induction names generalizing left right next with
  | nil => exact ⟨price .skip, price .skip, rfl, rfl⟩
  | cons name rest ih =>
    obtain ⟨l, r, leftLine, rightLine⟩ := ih left right next
    rcases produced : fakeMoves (width := 64) prio rest left right next with ⟨lp, rp, counter, lm, rm⟩
    rw [produced] at leftLine rightLine
    dsimp only at leftLine rightLine
    simp only [fakeMoves, produced]
    cases leftLookup : sptLookup name lm with
    | none =>
      cases rightLookup : sptLookup name rm with
      | none => exact ⟨l, r, leftLine, rightLine⟩
      | some rv =>
        refine ⟨l + price (fakeMove counter), r + price (.move (priority prio false) [(counter,rv)]), ?_, ?_⟩
        all_goals simp only [leftLookup, rightLookup, lineBound, leftLine, rightLine,
          fakeMove, isLeafProg, ssaReconciliationLeaf, if_true]
    | some lv =>
      cases rightLookup : sptLookup name rm with
      | none =>
        refine ⟨l + price (.move (priority prio true) [(counter,lv)]), r + price (fakeMove counter), ?_, ?_⟩
        all_goals simp only [leftLookup, rightLookup, lineBound, leftLine, rightLine,
          fakeMove, isLeafProg, ssaReconciliationLeaf, if_true]
      | some rv => exact ⟨l, r, leftLine, rightLine⟩

/-- Actual branch reconciliation programs have finite leaf sums, rather than
a program-size maximum or fixed cost per source control node. -/
theorem ssa_fix_inconsistencies_line (price : WordLangProgHOL (BitVec 64) → Nat)
    (prio : Option (Unit ⊕ Unit)) (left right : Spt Nat) (next : Nat) :
    ∃ l r,
      lineBound (ssaReconciliationLeaf price) (fixInconsistencies (width := 64) prio left right next).1 = some l ∧
      lineBound (ssaReconciliationLeaf price) (fixInconsistencies (width := 64) prio left right next).2.1 = some r := by
  let names := (sptToAList (sptUnion left right)).map Prod.fst
  rcases merged : mergeMoves names left right next with ⟨lm, rm, counter, leftMap, rightMap⟩
  obtain ⟨l, r, leftLine, rightLine⟩ := ssa_fake_moves_line price prio names leftMap rightMap counter
  rcases faked : fakeMoves (width := 64) prio names leftMap rightMap counter with ⟨lp, rp, nextOut, finalMap, finalRight⟩
  rw [faked] at leftLine rightLine
  refine ⟨price (.move (priority prio true) lm) + l, price (.move (priority prio false) rm) + r, ?_, ?_⟩
  all_goals simp only [fixInconsistencies, ← show names = (sptToAList (sptUnion left right)).map Prod.fst from rfl,
    merged, faked, lineBound, isLeafProg, ssaReconciliationLeaf, if_true, leftLine, rightLine]

/-- Executed reconciliation work is at most the sum of its exact emitted
leaf prices, for any pure target price with zero sequence overhead. -/
theorem ssa_reconciliation_line_cost {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → Nat)
    (seqZero : ∀ a b, price (.seq a b) = 0)
    (program : WordLangProgHOL (BitVec 64)) (n : Nat)
    (line : lineBound (ssaReconciliationLeaf price) program = some n)
    (source : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost (fun p _ => price p) program source ≤ n := by
  apply wordCost_le_lineBound (fun p _ => price p) (ssaReconciliationLeaf price)
    (fun a b _ => seqZero a b) ?_ program n line source
  intro p state amount leaf priced
  cases p <;> simp only [ssaReconciliationLeaf, reduceCtorEq, Option.some.injEq] at priced
  all_goals subst amount
  all_goals exact Nat.le_refl _

#print axioms ssa_fake_moves_line
#print axioms ssa_fix_inconsistencies_line
#print axioms ssa_reconciliation_line_cost
end InitECandidate.Runtime.FineCost
