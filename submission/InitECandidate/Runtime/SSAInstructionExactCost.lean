import InitECandidate.Runtime.SSAReconciliationLineCost
import InitECandidate.Runtime.SSAQuantitativeCost
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000
set_option pp.structureInstances false

/-- Every actual integer instruction fragment emitted by SSA is straight
line. Its local prices retain the actual operand registers and move pairs. -/
theorem ssa_instruction_exact_line (price : WordLangProgHOL (BitVec 64) → Nat)
    (instruction : WordLangInst (BitVec 64)) (map : Spt Nat) (next : Nat) :
    ∃ n, lineBound (ssaReconciliationLeaf price) (ssaCcTransInst instruction map next).1 = some n := by
  cases instruction with
  | skip | const _ _ =>
    simp [ssaCcTransInst, nextVarRename, lineBound, isLeafProg, ssaReconciliationLeaf]
  | arith operation =>
    cases operation with
    | binop op dst src operand | shift op dst src operand =>
      cases operand <;> simp [ssaCcTransInst, nextVarRename, lineBound, isLeafProg, ssaReconciliationLeaf]
    | _ => simp [ssaCcTransInst, nextVarRename, lineBound, isLeafProg, ssaReconciliationLeaf]
  | mem operation destination address =>
    cases address
    cases operation <;> simp [ssaCcTransInst, nextVarRename, lineBound, isLeafProg, ssaReconciliationLeaf]

/-- Exact-price SSA instruction interface. The original semantic witness is
retained, and the source atomic instruction pays its actual emitted fragment.
No fixed spill floor or per-pair surcharge is required by this theorem. -/
theorem ssa_quantitative_instruction_exact {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (instruction : WordLangInst (BitVec 64)) (source target : WordSemStateFiniteExact 64 C F)
    (map : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (seqZero : ∀ a b, TP (.seq a b) = 0)
    (localPrice : ssaReconciliationPrice TP (ssaCcTransInst instruction map next).1 ≤ SP (.inst instruction))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next map source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.inst instruction) = true ∧
      ssaMapOK next map ∧ ltOK tables) :
    SSAQuantitativeSimulation SP TP (.inst instruction) source target map next tables := by
  have semantics := ssaCcTransCorrectInst source target map next instruction tables h
  obtain ⟨permutation, post⟩ := ssa_semantic_witness (.inst instruction) source target map next tables semantics
  obtain ⟨n, line⟩ := ssa_instruction_exact_line TP instruction map next
  have bound := ssa_reconciliation_line_cost TP seqZero (ssaCcTransInst instruction map next).1 n line target
  have price : n ≤ SP (.inst instruction) := by
    simpa only [ssaReconciliationPrice, line, Option.getD_some] using localPrice
  refine ⟨permutation, ?_⟩
  rcases post with error | ⟨same, frame, locals⟩
  · exact Or.inl error
  · refine Or.inr ⟨same, frame, locals, ?_⟩
    rw [wordExecutionCost_atomic _ (.inst instruction) _ rfl]
    have compiled : (ssaCcTrans (.inst instruction) map next tables).1 = (ssaCcTransInst instruction map next).1 := by
      simp only [ssaCcTrans]
    rw [compiled]
    exact bound.trans price

#print axioms ssa_instruction_exact_line
#print axioms ssa_quantitative_instruction_exact
end InitECandidate.Runtime.FineCost
