import InitECandidate.Runtime.SSAQuantitativeCost
import InitECandidate.Runtime.WordLineCost
import InitECandidate.Runtime.WordCseAtomicCost
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticCorrect

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 8000000
set_option pp.structureInstances false

/-- Exact leaf sum of emitted straight-line SSA code. Only the Seq heads are
omitted; operands, move pairs and operation sizes remain in the leaf price. -/
def ssaAtomicPrice (TP : WordLangProgHOL (BitVec 64) → Nat)
    (p : WordLangProgHOL (BitVec 64)) : Nat :=
  (lineBound (fun q => some (TP q)) p).getD 0

/-- Actual SSA compilation of any atomic source statement is straight-line,
including live-root moves around allocation, installation and FFI. -/
theorem ssa_atomic_compiled_line (TP : WordLangProgHOL (BitVec 64) → Nat)
    (p : WordLangProgHOL (BitVec 64)) (map : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit)) (atomic : wordCostAtomic p = true) :
    ∃ n, lineBound (fun q => some (TP q)) (ssaCcTrans p map next tables).1 = some n := by
  cases p with
  | seq | ite | loop | call | mustTerminate => simp [wordCostAtomic] at atomic
  | inst instruction =>
    cases instruction with
    | skip | const _ _ =>
      simp [ssaCcTrans,ssaCcTransInst,nextVarRename,lineBound,isLeafProg]
    | arith operation =>
      cases operation with
      | binop op dst src operand | shift op dst src operand =>
        cases operand <;> simp [ssaCcTrans,ssaCcTransInst,nextVarRename,lineBound,isLeafProg]
      | _ => simp [ssaCcTrans,ssaCcTransInst,nextVarRename,lineBound,isLeafProg]
    | mem operation destination address =>
      cases address
      cases operation <;> simp [ssaCcTrans,ssaCcTransInst,nextVarRename,lineBound,isLeafProg]
  | «break» label | «continue» label =>
    simp only [ssaCcTrans]
    cases found : tables[label]? with
    | none => simp [lineBound,isLeafProg]
    | some table =>
      rcases table with ⟨dest,entries,exits⟩
      unfold ssaReconcile
      dsimp only
      split_ifs <;> simp [lineBound,isLeafProg]
  | shareInst operation destination address =>
    simp [ssaCcTrans,nextVarRename,lineBound,isLeafProg]
    split <;> simp [lineBound,isLeafProg]
  | _ => simp [ssaCcTrans,listNextVarRenameMove,nextVarRename,lineBound,isLeafProg]

/-- All atomic SSA constructors retain the original semantic permutation and
pay the actual emitted leaf sum. No callee/body IH, target run, global code
maximum or fixed spill coefficient is required. -/
theorem ssa_quantitative_atomic {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (p : WordLangProgHOL (BitVec 64)) (source target : WordSemStateFiniteExact 64 C F)
    (map : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (atomic : wordCostAtomic p = true) (seqZero : ∀ a b, TP (.seq a b) = 0)
    (localPrice : ssaAtomicPrice TP (ssaCcTrans p map next tables).1 ≤ SP p)
    (premises : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next map source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun key => decide (key < next)) p = true ∧
      ssaMapOK next map ∧ ltOK tables) :
    SSAQuantitativeSimulation SP TP p source target map next tables := by
  obtain ⟨permutation,post⟩ := ssa_semantic_witness p source target map next tables
    (ssaCcTransCorrect p source target map next tables premises)
  obtain ⟨n,line⟩ := ssa_atomic_compiled_line TP p map next tables atomic
  refine ⟨permutation,?_⟩
  rcases post with error | ⟨same,frame,locals⟩
  · exact Or.inl error
  · refine Or.inr ⟨same,frame,locals,?_⟩
    rw [wordExecutionCost_atomic _ p _ atomic]
    have price : n ≤ SP p := by
      simpa only [ssaAtomicPrice,line,Option.getD_some] using localPrice
    have work : wordExecutionCost (fun q _ => TP q) (ssaCcTrans p map next tables).1 target ≤ n := by
      exact wordCost_le_lineBound (fun q _ => TP q) (fun q => some (TP q))
        (fun a b _ => seqZero a b)
        (fun q _ k _ eq => Nat.le_of_eq (Option.some.inj eq))
        (ssaCcTrans p map next tables).1 n line target
    exact work.trans price

#print axioms ssa_atomic_compiled_line
#print axioms ssa_quantitative_atomic
end InitECandidate.Runtime.FineCost
