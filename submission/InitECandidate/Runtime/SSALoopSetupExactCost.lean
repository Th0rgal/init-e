import InitECandidate.Runtime.SSAReconciliationLineCost
import InitECandidate.Runtime.SSALoopBodyEntry
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALoopSetup
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000
set_option pp.structureInstances false

/-- Exact straight-line sum for the fake initializations in loop setup. -/
theorem ssa_fake_chain_line (price : WordLangProgHOL (BitVec 64) → Nat) (registers : List Nat) :
    ∃ n, lineBound (ssaReconciliationLeaf price)
      ((registers.map fun r => (fakeMove r : WordLangProgHOL (BitVec 64))).foldr .seq .skip) = some n := by
  induction registers with
  | nil => exact ⟨price .skip, rfl⟩
  | cons register rest ih =>
    obtain ⟨n, line⟩ := ih
    refine ⟨price (fakeMove register) + n, ?_⟩
    simp only [List.map_cons, List.foldr_cons]
    rw [lineBound, line]
    rfl

/-- Every actual SSA loop setup has a finite exact emitted leaf sum. It is
one entry fragment, kept separate from the repeated loop body. -/
theorem ssa_loop_setup_line (price : WordLangProgHOL (BitVec 64) → Nat)
    (names exits : Spt Unit) (map : Spt Nat) (next : Nat) :
    ∃ n, lineBound (ssaReconciliationLeaf price) (loopSetup (width := 64) names exits map next).1 = some n := by
  unfold loopSetup
  dsimp only
  generalize keysEq : (sptToAList (sptUnion names exits)).map Prod.fst = keys
  rcases extended : listNextVarRename (keys.filter (fun v => (sptLookup v map).isNone)) map next with
    ⟨registers, extendedMap, extendedNext⟩
  dsimp only
  rcases refreshed : listNextVarRenameMove (width := 64) extendedMap extendedNext
      (keys.filter (fun v => (sptLookup v map).isSome)) with ⟨moves, finalMap, finalNext⟩
  obtain ⟨n, fakeLine⟩ := ssa_fake_chain_line price registers
  have moveLine : lineBound (ssaReconciliationLeaf price) moves = some (price moves) := by
    have shape := congrArg Prod.fst refreshed
    simp only [listNextVarRenameMove] at shape
    rw [← shape]
    rfl
  refine ⟨n + price moves, ?_⟩
  simp only [refreshed, lineBound, fakeLine, moveLine]

/-- Actual setup semantics and complete refreshed loop-entry facts together
with its one-time exact-price work. Compiler shape discharges the straight
fragment certificate; no target execution or whole-run budget is a premise. -/
theorem loopSetupCorrect_exact_cost {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → Nat) (seqZero : ∀ p q, price (.seq p q) = 0)
    (source target : WordSemStateFiniteExact 64 C F) (map : Spt Nat) (next : Nat)
    (names exits : Spt Unit) (setup : WordLangProgHOL (BitVec 64)) (refreshed : Spt Nat) (nextRefreshed : Nat)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target)
    (related : ssaLocalsRel next map source.locals target.locals)
    (valid : ssaMapOK next map) (allocated : isAllocVar next)
    (produced : loopSetup names exits map next = (setup, refreshed, nextRefreshed)) :
    ∃ after, evaluate setup target = (none, after) ∧
      Flapjack.WordAlloc.wordStateEqRel source after ∧
      ssaLocalsRel nextRefreshed refreshed source.locals after.locals ∧
      Flapjack.WordAlloc.strongLocalsRel (optionLookup refreshed) (sptDomain names) source.locals after.locals ∧
      next ≤ nextRefreshed ∧ isAllocVar nextRefreshed ∧ ssaMapOK nextRefreshed refreshed ∧
      sptDomain refreshed = (fun key => sptDomain map key ∨ sptDomain (sptUnion names exits) key) ∧
      (∀ x y, sptDomain names x → sptDomain names y →
        optionLookup refreshed x = optionLookup refreshed y → x = y) ∧
      (∀ x y, sptDomain exits x → sptDomain exits y →
        optionLookup refreshed x = optionLookup refreshed y → x = y) ∧
      (∀ key, sptDomain refreshed key → sptDomain after.locals (optionLookup refreshed key)) ∧
      wordExecutionCost (fun p _ => price p) setup target ≤ ssaReconciliationPrice price setup := by
  obtain ⟨after, run, frameAfter, locals, grows, allocAfter, validAfter, domain, entryInj, exitInj, present⟩ :=
    loopSetupCorrect source target map next names exits setup refreshed nextRefreshed
      ⟨frame, related, valid, allocated, produced⟩
  obtain ⟨n, line⟩ := ssa_loop_setup_line price names exits map next
  rw [produced] at line
  dsimp only at line
  have cost := ssa_reconciliation_line_cost price seqZero setup n line target
  have exactPrice : ssaReconciliationPrice price setup = n := by
    simp only [ssaReconciliationPrice, line, Option.getD_some]
  rw [← exactPrice] at cost
  exact ⟨after, run, frameAfter, locals, ssa_locals_strong _ _ _ _ _ locals,
    grows, allocAfter, validAfter, domain, entryInj, exitInj, present, cost⟩

#print axioms ssa_fake_chain_line
#print axioms ssa_loop_setup_line
#print axioms loopSetupCorrect_exact_cost
end InitECandidate.Runtime.FineCost
