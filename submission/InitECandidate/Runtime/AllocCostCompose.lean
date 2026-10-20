import InitECandidate.Runtime.AllocCostPasses
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.WordAlloc Flapjack.WordAlloc
open Flapjack.Compiler.Backend.WordInst
open InitECandidate.Runtime.WordToStack

/-!
# Composed SSA / three-to-two / allocation budget

The selected straight-line fragment is first renamed by SSA (prologue plus the
instruction moves measured in `AllocCostSSA`), then rewritten by three-to-two
(one move per rewritten instruction) and finally coloured by the allocator
(no inserted Word instruction).  The composition below adds exactly those
local charges; it never multiplies by a whole-program AST, code-table, bitmap
or ROM size.
-/

/-- SSA keeps the number of instructions eligible for three-to-two rewriting. -/
theorem threeToTwoSites_ssaInst (instruction : Flapjack.WordLangInst (BitVec 64))
    (ssa : Spt Nat) (na : Nat) :
    threeToTwoSites (ssaCcTransInst instruction ssa na).1 ≤
      threeToTwoSites (.inst instruction) := by
  cases instruction with
  | arith operation =>
    cases operation with
    | binop op destination source right =>
      cases right <;> simp [ssaCcTransInst, threeToTwoSites, threeToTwoRewrites]
    | shift sh destination source right =>
      cases right <;> simp [ssaCcTransInst, threeToTwoSites, threeToTwoRewrites]
    | _ => simp [ssaCcTransInst, threeToTwoSites, threeToTwoRewrites]
  | mem operation destination address =>
    cases operation <;> simp [ssaCcTransInst, threeToTwoSites, threeToTwoRewrites]
  | const reg value => simp [ssaCcTransInst, threeToTwoSites, threeToTwoRewrites]
  | _ => simp [ssaCcTransInst, threeToTwoSites, threeToTwoRewrites]

/-- SSA's renamings and inserted moves introduce no new three-to-two sites. -/
theorem threeToTwoSites_ssa_body (p : WordLangProgHOL (BitVec 64))
    (supported : selectionStraightLine p = true) (ssa : Spt Nat) (na : Nat)
    (lt : List (Spt Nat × Spt Unit × Spt Unit)) :
    threeToTwoSites (ssaCcTrans p ssa na lt).1 ≤ threeToTwoSites p := by
  cases p <;> simp only [selectionStraightLine, Bool.and_eq_true, decide_eq_true_eq] at supported
  all_goals try contradiction
  case skip => rw [ssaCcTrans]; simp [threeToTwoSites]
  case get destination store => rw [ssaCcTrans]; simp [threeToTwoSites]
  case opCurrHeap operator destination source => rw [ssaCcTrans]; simp [threeToTwoSites]
  case move priority moves => rw [ssaCcTrans]; simp [threeToTwoSites]
  case inst instruction =>
    rw [ssaCcTrans]
    exact threeToTwoSites_ssaInst instruction ssa na
  case seq first second =>
    rcases h : ssaCcTrans first ssa na lt with ⟨p1, ssa', na'⟩
    have firstBound := threeToTwoSites_ssa_body first supported.1 ssa na lt
    rw [h] at firstBound
    dsimp only at firstBound
    have secondBound := threeToTwoSites_ssa_body second supported.2 ssa' na' lt
    rw [ssaCcTrans, h]
    simp only [threeToTwoSites]
    omega
termination_by sizeOf p
decreasing_by all_goals (subst_vars; simp_wf; try omega)

/-- The SSA argument prologue is a move and has no rewrite sites. -/
theorem threeToTwoSites_fullSsa (count : Nat) (p : WordLangProgHOL (BitVec 64))
    (supported : selectionStraightLine p = true) :
    threeToTwoSites (fullSsaCcTrans count p) ≤ threeToTwoSites p := by
  rcases produced : setupSSA (outputWidth := 64) count (limitVar p) p with ⟨mov, ssa, na⟩
  have moveShape := (setupSSA_move_nodeCost count (limitVar p) p).1
  rw [produced] at moveShape
  have bodyBound := threeToTwoSites_ssa_body p supported ssa na []
  simp only [fullSsaCcTrans, produced, threeToTwoSites, moveShape]
  omega

/-- End-to-end local budget for the straight-line fragment through SSA,
three-to-two registers and allocation. -/
theorem compiled_fragment_nodeCost (count : Nat)
    (config : Flapjack.Compiler.Encoders.Asm.AsmConfigExact 64)
    (fc algorithm limit : Nat) (enabled : Bool)
    (p : WordLangProgHOL (BitVec 64)) (supported : selectionStraightLine p = true)
    (colour : Option (Spt Nat)) :
    wordNodeCost (wordAlloc fc config algorithm limit
      (threeToTwoRegProg enabled (fullSsaCcTrans count p)) colour) ≤
      wordNodeCost p + (2 + count) + ssaStraightOverhead p + 3 * threeToTwoSites p := by
  have allocBound := wordAlloc_nodeCost_le fc config algorithm limit
    (threeToTwoRegProg enabled (fullSsaCcTrans count p)) colour
  have threeBound := threeToTwoRegProg_nodeCost enabled (fullSsaCcTrans count p)
  have ssaBound := fullSsa_straight_cost count p supported
  have sitesBound := threeToTwoSites_fullSsa count p supported
  omega

#print axioms compiled_fragment_nodeCost
#print axioms threeToTwoSites_fullSsa
end InitECandidate.Runtime.FineCost
