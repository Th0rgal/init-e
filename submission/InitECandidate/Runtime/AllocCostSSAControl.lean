import InitECandidate.Runtime.AllocCostReconcile
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.WordAlloc
open InitECandidate.Runtime.WordToStack

/-!
# SSA control-flow *syntax* envelopes

This module bounds the syntactic `wordNodeCost` of the programs that SSA emits
at loop headers, back-edges, call sites and `break`/`continue`.  These are
static per-site envelopes: the loop theorem counts the body syntax once and
does **not** by itself prove executed-cost transfer for repeated iterations.
The actual executed charge is in `AllocCostSSAExecuted`, where each
reconciliation is evaluated by `wordPathWork` at its concrete state.  The
whole-loop iteration induction is an explicit remaining premise, not hidden
here.
-/

private theorem reconcile_seq_budget (a b : Nat) (h : b ≤ a + 1) :
    1 + b + 1 ≤ 1 + (a + 4) := by
  omega

theorem ssaCcTrans_break_nodeCost_le (n : Nat) (ssa : Spt Nat) (next : Nat)
    (lt : List (Spt Nat × Spt Unit × Spt Unit))
    (target : Spt Nat) (names exitNames : Spt Unit)
    (moves : WordLangProgHOL (BitVec 64))
    (hlt : lt[n]? = some (target, names, exitNames))
    (hmoves : ssaReconcile (width := 64) ssa target exitNames = moves)
    (hcost : wordNodeCost moves ≤ 1 + (sptToAList exitNames).length) :
    wordNodeCost (ssaCcTrans (width := 64) (.break n) ssa next lt).1 ≤
      wordNodeCost (WordLangProgHOL.break n) +
        ((sptToAList exitNames).length + 4) := by
  rw [ssaCcTrans]
  rw [hlt]
  dsimp only
  rw [hmoves]
  split
  · simp only [wordNodeCost]
    omega
  · simp only [wordNodeCost]
    omega

theorem ssaCcTrans_continue_nodeCost_le (n : Nat) (ssa : Spt Nat) (next : Nat)
    (lt : List (Spt Nat × Spt Unit × Spt Unit))
    (target : Spt Nat) (names exitNames : Spt Unit)
    (moves : WordLangProgHOL (BitVec 64))
    (hlt : lt[n]? = some (target, names, exitNames))
    (hmoves : ssaReconcile (width := 64) ssa target names = moves)
    (hcost : wordNodeCost moves ≤ 1 + (sptToAList names).length) :
    wordNodeCost (ssaCcTrans (width := 64) (.continue n) ssa next lt).1 ≤
      wordNodeCost (WordLangProgHOL.continue n) +
        ((sptToAList names).length + 4) := by
  rw [ssaCcTrans]
  rw [hlt]
  dsimp only
  rw [hmoves]
  split
  · simp only [wordNodeCost]
    omega
  · simp only [wordNodeCost]
    omega

theorem ssaCcTrans_break_target_nodeCost_le (n : Nat) (ssa : Spt Nat) (next : Nat)
    (lt : List (Spt Nat × Spt Unit × Spt Unit))
    (target : Spt Nat) (names exitNames : Spt Unit)
    (hlt : lt[n]? = some (target, names, exitNames)) :
    wordNodeCost (ssaCcTrans (width := 64) (.break n) ssa next lt).1 ≤
      wordNodeCost (WordLangProgHOL.break n) +
        ((sptToAList exitNames).length + 4) :=
  ssaCcTrans_break_nodeCost_le n ssa next lt target names exitNames
    (ssaReconcile (width := 64) ssa target exitNames) hlt rfl
    (ssaReconcile_nodeCost_le ssa target exitNames)

theorem ssaCcTrans_continue_target_nodeCost_le (n : Nat) (ssa : Spt Nat) (next : Nat)
    (lt : List (Spt Nat × Spt Unit × Spt Unit))
    (target : Spt Nat) (names exitNames : Spt Unit)
    (hlt : lt[n]? = some (target, names, exitNames)) :
    wordNodeCost (ssaCcTrans (width := 64) (.continue n) ssa next lt).1 ≤
      wordNodeCost (WordLangProgHOL.continue n) +
        ((sptToAList names).length + 4) :=
  ssaCcTrans_continue_nodeCost_le n ssa next lt target names exitNames
    (ssaReconcile (width := 64) ssa target names) hlt rfl
    (ssaReconcile_nodeCost_le ssa target names)

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

#print axioms ssaCcTrans_break_target_nodeCost_le
#print axioms ssaCcTrans_continue_target_nodeCost_le
#print axioms ssaCcTrans_break_nodeCost_le
#print axioms ssaCcTrans_continue_nodeCost_le
#print axioms ssaCcTrans_call_none_nodeCost_le
#print axioms ssaCcTrans_loop_nodeCost_le
end InitECandidate.Runtime.FineCost
