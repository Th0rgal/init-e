import InitECandidate.Runtime.AllocCostReconcile
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.WordAlloc
open InitECandidate.Runtime.WordToStack

/-!
# SSA control-flow reconciliation

Break and continue reconcile the current map with the target loop map; a loop
pays for its setup program and its back-edge reconciliation.  The loop theorem
is relative to an already established body bound, so it composes with any
induction or scheduling argument rather than assuming a whole-program maximum.
-/

private theorem reconcile_seq_budget (a b : Nat) (h : b ≤ a + 1) :
    1 + b + 1 ≤ 1 + (a + 4) := by
  omega

theorem ssaCcTrans_call_none_nodeCost_le (dest : Nat)
    (args : List Nat)
    (h : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (ssa : Spt Nat) (next : Nat)
    (lt : List (Spt Nat × Spt Unit × Spt Unit)) :
    wordNodeCost (ssaCcTrans (width := 64) (.call none dest args h) ssa next lt).1 ≤
      wordNodeCost (.call none dest args h) + (4 + args.length) := by
  rw [ssaCcTrans]
  dsimp only
  cases h with
  | none =>
    simp only [wordNodeCost, List.length_map, List.length_zip, List.length_range]
    omega
  | some handler =>
    rcases handler with ⟨n, code, l1, l2⟩
    simp only [wordNodeCost, List.length_map, List.length_zip, List.length_range]
    omega

/-- A loop costs its setup plus the already bounded body and the back-edge
reconciliation. -/
theorem ssaCcTrans_loop_nodeCost_le (names exitNames : Spt Unit)
    (body : WordLangProgHOL (BitVec 64)) (ssa : Spt Nat) (next : Nat)
    (lt : List (Spt Nat × Spt Unit × Spt Unit))
    (setup : WordLangProgHOL (BitVec 64)) (ssaRefreshed : Spt Nat) (naRefreshed : Nat)
    (hsetup : loopSetup (width := 64) names exitNames ssa next =
      (setup, ssaRefreshed, naRefreshed))
    (body' : WordLangProgHOL (BitVec 64)) (ssa' : Spt Nat) (na' : Nat)
    (hbody : ssaCcTrans (width := 64) body (sptInter ssaRefreshed names) naRefreshed
      ((ssaRefreshed, names, exitNames) :: lt) = (body', ssa', na'))
    (bodyBudget : Nat)
    (hbodyCost : wordNodeCost body' ≤ wordNodeCost body + bodyBudget) :
    wordNodeCost (ssaCcTrans (width := 64) (.loop names body exitNames) ssa next lt).1 ≤
      wordNodeCost (.loop names body exitNames) +
        (8 + 3 * (sptToAList (sptUnion names exitNames)).length +
          (sptToAList names).length + bodyBudget) := by
  rw [ssaCcTrans]
  rw [hsetup]
  dsimp only
  rw [hbody]
  dsimp only
  have setupBound := loopSetup_nodeCost_le names exitNames ssa next
  rw [hsetup] at setupBound
  dsimp only at setupBound
  have backBound := ssaReconcile_nodeCost_le ssa' ssaRefreshed names
  split
  · simp only [wordNodeCost]
    omega
  · simp only [wordNodeCost]
    omega

#print axioms ssaCcTrans_call_none_nodeCost_le
#print axioms ssaCcTrans_loop_nodeCost_le
end InitECandidate.Runtime.FineCost
