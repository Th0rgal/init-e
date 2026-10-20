import InitECandidate.Runtime.AllocCostModel
import Flapjack.Compiler.Backend.WordAlloc.SSACcTrans
import Flapjack.Compiler.Backend.WordAlloc.SSASetup
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.WordAlloc Flapjack.Compiler.Backend.WordInst
open InitECandidate.Runtime.WordToStack

/-!
# SSA/renaming work transfer on selected straight-line fragments

`fullSsaCcTrans` prefixes a parallel argument move and renames variables.  This
module measures the moves it inserts locally.  The prologue has exactly the
argument count.  An instruction that SSA rewrites around fixed temporaries adds
a constant number of move/sequence nodes, measured by `ssaInstOverhead`; no
whole-program variable-map size, AST maximum or code-table size is used.
-/

/-- Added node cost of the moves SSA inserts around one instruction.  Each
inserted parallel move contributes one move node plus one unit per moved word,
and each enclosing `Seq` contributes one control node. -/
def ssaInstOverhead : WordLangInst (BitVec 64) → Nat
  | .arith (.shift _ _ _ (.reg _)) => 3
  | .arith (.addCarry _ _ _ _) => 6
  | .arith (.addOverflow _ _ _ _) => 3
  | .arith (.subOverflow _ _ _ _) => 3
  | .arith (.longMul _ _ _ _) => 8
  | .arith (.longDiv _ _ _ _ _) => 8
  | _ => 0

/-- Inserted-move node budget over the selected straight-line fragment. -/
def ssaStraightOverhead : WordLangProgHOL (BitVec 64) → Nat
  | .inst instruction => ssaInstOverhead instruction
  | .seq first second => ssaStraightOverhead first + ssaStraightOverhead second
  | _ => 0
termination_by p => sizeOf p

theorem ssaInstOverhead_le_eight (instruction : WordLangInst (BitVec 64)) :
    ssaInstOverhead instruction ≤ 8 := by
  cases instruction with
  | arith operation => cases operation <;> (simp [ssaInstOverhead]; try split <;> omega)
  | _ => simp [ssaInstOverhead]

theorem listNextVarRename_length (names : List Nat) (ssa : Spt Nat) (next : Nat) :
    (listNextVarRename names ssa next).1.length = names.length := by
  induction names generalizing ssa next with
  | nil => simp [listNextVarRename]
  | cons name rest ih =>
    simp [listNextVarRename, nextVarRename, ih]

theorem evenList_length (count : Nat) : (evenList count).length = count := by
  simp [evenList]

theorem setupSSA_move_nodeCost {inputWidth : Nat} [NeZero inputWidth]
    (count limit : Nat) (program : WordLangProgHOL (BitVec inputWidth)) :
    (setupSSA (outputWidth := 64) count limit program).1 = .move 1
      (((listNextVarRename (evenList count) .ln limit).1).zip (evenList count)) ∧
    wordNodeCost (setupSSA (outputWidth := 64) count limit program).1 = 1 + count := by
  constructor
  · rfl
  · simp only [setupSSA, wordNodeCost]
    rw [List.length_zip, listNextVarRename_length, evenList_length]
    omega

/-- SSA instruction rewrite: renames plus the locally inserted moves. -/
theorem ssa_inst_cost (instruction : WordLangInst (BitVec 64)) (ssa : Spt Nat) (na : Nat) :
    wordNodeCost (ssaCcTransInst instruction ssa na).1 ≤
      1 + ssaInstOverhead instruction := by
  cases instruction with
  | arith operation =>
    cases operation with
    | binop op r1 r2 ri =>
      cases ri <;> simp [ssaCcTransInst, wordNodeCost, ssaInstOverhead]
    | shift sh r1 r2 ri =>
      cases ri <;> simp [ssaCcTransInst, wordNodeCost, ssaInstOverhead]
    | div r1 r2 r3 => simp [ssaCcTransInst, wordNodeCost, ssaInstOverhead]
    | addCarry r1 r2 r3 r4 => simp [ssaCcTransInst, wordNodeCost, ssaInstOverhead]
    | addOverflow r1 r2 r3 r4 => simp [ssaCcTransInst, wordNodeCost, ssaInstOverhead]
    | subOverflow r1 r2 r3 r4 => simp [ssaCcTransInst, wordNodeCost, ssaInstOverhead]
    | longMul r1 r2 r3 r4 => simp [ssaCcTransInst, wordNodeCost, ssaInstOverhead]
    | longDiv r1 r2 r3 r4 r5 => simp [ssaCcTransInst, wordNodeCost, ssaInstOverhead]
  | mem operation destination address =>
    cases operation <;> simp [ssaCcTransInst, wordNodeCost, ssaInstOverhead]
  | const reg value => simp [ssaCcTransInst, wordNodeCost, ssaInstOverhead]
  | _ => simp [ssaCcTransInst, wordNodeCost, ssaInstOverhead]

/-- Inserted-move sites are bounded by the selected leaf count. -/
theorem ssaStraightOverhead_le_selectionLeaves (p : WordLangProgHOL (BitVec 64))
    (supported : selectionStraightLine p = true) :
    ssaStraightOverhead p ≤ 8 * selectionLeaves p := by
  cases p <;> simp only [selectionStraightLine, Bool.and_eq_true, decide_eq_true_eq] at supported
  all_goals try contradiction
  case skip => simp [ssaStraightOverhead, selectionLeaves]
  case inst instruction =>
    have bound := ssaInstOverhead_le_eight instruction
    simp only [ssaStraightOverhead, selectionLeaves]
    omega
  case get destination store => simp [ssaStraightOverhead, selectionLeaves]
  case opCurrHeap operator destination source => simp [ssaStraightOverhead, selectionLeaves]
  case move priority moves => simp [ssaStraightOverhead, selectionLeaves]
  case seq first second =>
    have firstBound := ssaStraightOverhead_le_selectionLeaves first supported.1
    have secondBound := ssaStraightOverhead_le_selectionLeaves second supported.2
    simp only [ssaStraightOverhead, selectionLeaves]
    omega
termination_by sizeOf p
decreasing_by all_goals (subst_vars; simp_wf; try omega)

/-- Body transfer: SSA renaming adds only the measured instruction moves. -/
theorem ssa_straight_body_cost (p : WordLangProgHOL (BitVec 64))
    (supported : selectionStraightLine p = true) (ssa : Spt Nat) (na : Nat)
    (lt : List (Spt Nat × Spt Unit × Spt Unit)) :
    wordNodeCost (ssaCcTrans p ssa na lt).1 ≤
      wordNodeCost p + ssaStraightOverhead p := by
  cases p <;> simp only [selectionStraightLine, Bool.and_eq_true, decide_eq_true_eq] at supported
  all_goals try contradiction
  case skip => rw [ssaCcTrans]; simp [wordNodeCost, ssaStraightOverhead]
  case get destination store =>
    rw [ssaCcTrans]; simp [wordNodeCost, ssaStraightOverhead]
  case opCurrHeap operator destination source =>
    rw [ssaCcTrans]; simp [wordNodeCost, ssaStraightOverhead]
  case move priority moves =>
    rw [ssaCcTrans]
    dsimp only
    simp only [wordNodeCost, ssaStraightOverhead]
    have hlen : (listNextVarRename (moves.map Prod.fst) ssa na).1.length = moves.length := by
      rw [listNextVarRename_length]
      simp
    have hzip : ((listNextVarRename (moves.map Prod.fst) ssa na).1.zip
        ((moves.map Prod.snd).map (optionLookup ssa))).length ≤ moves.length := by
      rw [List.length_zip, hlen]
      exact Nat.min_le_left _ _
    omega
  case inst instruction =>
    rw [ssaCcTrans]
    have bound := ssa_inst_cost instruction ssa na
    simp only [wordNodeCost, ssaStraightOverhead]
    omega
  case seq first second =>
    rcases h : ssaCcTrans first ssa na lt with ⟨p1, ssa', na'⟩
    have firstBound := ssa_straight_body_cost first supported.1 ssa na lt
    rw [h] at firstBound
    dsimp only at firstBound
    have secondBound := ssa_straight_body_cost second supported.2 ssa' na' lt
    rw [ssaCcTrans, h]
    simp only [wordNodeCost, ssaStraightOverhead]
    omega
termination_by sizeOf p
decreasing_by all_goals (subst_vars; simp_wf; try omega)

/-- Complete `fullSsaCcTrans` transfer: prologue `count` move words, its move
node and the enclosing sequence node, plus the body's instruction moves. -/
theorem fullSsa_straight_cost (count : Nat) (p : WordLangProgHOL (BitVec 64))
    (supported : selectionStraightLine p = true) :
    wordNodeCost (fullSsaCcTrans count p) ≤
      wordNodeCost p + (2 + count) + ssaStraightOverhead p := by
  rcases produced : setupSSA (outputWidth := 64) count (limitVar p) p with ⟨mov, ssa, na⟩
  have moveCost : wordNodeCost mov = 1 + count := by
    have := setupSSA_move_nodeCost count (limitVar p) p
    rw [produced] at this
    exact this.2
  have bodyBound := ssa_straight_body_cost p supported ssa na []
  have expanded : wordNodeCost (fullSsaCcTrans count p) =
      1 + wordNodeCost mov + wordNodeCost (ssaCcTrans p ssa na []).1 := by
    simp only [fullSsaCcTrans, produced, wordNodeCost]
  rw [expanded, moveCost]
  omega

#print axioms fullSsa_straight_cost
#print axioms ssa_straight_body_cost
#print axioms ssaStraightOverhead_le_selectionLeaves
end InitECandidate.Runtime.FineCost
