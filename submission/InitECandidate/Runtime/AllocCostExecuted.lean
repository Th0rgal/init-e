import InitECandidate.Runtime.AllocCostCompose
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.WordAlloc Flapjack.WordAlloc Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend.WordInst
open InitECandidate.Runtime.WordToStack

/-!
# Executed-path bridge for optimized straight-line fragments

`wordPathWork` follows the actually selected branches.  The SSA, three-to-two
and allocation outputs of a selected expression fragment remain in the
`wordStraightFragment` grammar: skip, arbitrary parallel moves, single
instructions, `Get`, `OpCurrHeap` and sequences.  On that grammar the executed
path budget is bounded by `wordNodeCost`, so `compiled_fragment_nodeCost`
transfers to the actual executed run, not merely to a static AST count.
-/

/-- Straight-line fragment grammar after SSA: parallel moves may have any
length here, unlike the raw selector's singleton-move grammar. -/
def wordStraightFragment : WordLangProgHOL (BitVec 64) → Bool
  | .skip | .inst _ | .get _ _ | .opCurrHeap _ _ _ => true
  | .move _ _ => true
  | .seq first second => wordStraightFragment first && wordStraightFragment second
  | _ => false
termination_by p => sizeOf p

theorem wordPathWork_le_nodeCost_straight {C F : Type}
    (p : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (supported : wordStraightFragment p = true) :
    wordPathWork p source ≤ wordNodeCost p := by
  cases p <;> simp only [wordStraightFragment, Bool.and_eq_true] at supported
  all_goals try contradiction
  all_goals try (simp only [wordPathWork, wordNodeCost]; omega)
  case seq first second =>
    have firstBound := wordPathWork_le_nodeCost_straight first source supported.1
    rw [wordPathWork_seq]
    simp only [wordNodeCost]
    cases run : evaluate first source with
    | mk result middle =>
      cases result with
      | none =>
        have secondBound := wordPathWork_le_nodeCost_straight second middle supported.2
        dsimp only
        omega
      | some value => dsimp only; omega
termination_by sizeOf p
decreasing_by all_goals (subst_vars; simp_wf; try omega)

/-- SSA instruction output stays in the straight-line grammar. -/
theorem ssaInstStraight (instruction : WordLangInst (BitVec 64)) (ssa : Spt Nat) (na : Nat) :
    wordStraightFragment (ssaCcTransInst instruction ssa na).1 = true := by
  cases instruction with
  | arith operation =>
    cases operation with
    | binop op r1 r2 ri => cases ri <;> simp [ssaCcTransInst, wordStraightFragment]
    | shift sh r1 r2 ri => cases ri <;> simp [ssaCcTransInst, wordStraightFragment]
    | _ => simp [ssaCcTransInst, wordStraightFragment]
  | mem operation destination address =>
    cases operation <;> simp [ssaCcTransInst, wordStraightFragment]
  | const reg value => simp [ssaCcTransInst, wordStraightFragment]
  | _ => simp [ssaCcTransInst, wordStraightFragment]

/-- SSA body output on a selected straight-line fragment is straight-line. -/
theorem ssaStraightFragment (p : WordLangProgHOL (BitVec 64))
    (supported : selectionStraightLine p = true) (ssa : Spt Nat) (na : Nat)
    (lt : List (Spt Nat × Spt Unit × Spt Unit)) :
    wordStraightFragment (ssaCcTrans p ssa na lt).1 = true := by
  cases p <;> simp only [selectionStraightLine, Bool.and_eq_true, decide_eq_true_eq] at supported
  all_goals try contradiction
  case skip => rw [ssaCcTrans]; simp [wordStraightFragment]
  case get destination store => rw [ssaCcTrans]; simp [wordStraightFragment]
  case opCurrHeap operator destination source => rw [ssaCcTrans]; simp [wordStraightFragment]
  case move priority moves => rw [ssaCcTrans]; simp [wordStraightFragment]
  case inst instruction =>
    rw [ssaCcTrans]
    exact ssaInstStraight instruction ssa na
  case seq first second =>
    rcases h : ssaCcTrans first ssa na lt with ⟨p1, ssa', na'⟩
    have firstStraight := ssaStraightFragment first supported.1 ssa na lt
    rw [h] at firstStraight
    have secondStraight := ssaStraightFragment second supported.2 ssa' na' lt
    rw [ssaCcTrans, h]
    simp only [wordStraightFragment]
    rw [firstStraight, secondStraight]
    rfl
termination_by sizeOf p
decreasing_by all_goals (subst_vars; simp_wf; try omega)

theorem fullSsaStraightFragment (count : Nat) (p : WordLangProgHOL (BitVec 64))
    (supported : selectionStraightLine p = true) :
    wordStraightFragment (fullSsaCcTrans count p) = true := by
  rcases produced : setupSSA (outputWidth := 64) count (limitVar p) p with ⟨mov, ssa, na⟩
  have bodyStraight := ssaStraightFragment p supported ssa na []
  have moveShape := (setupSSA_move_nodeCost count (limitVar p) p).1
  rw [produced] at moveShape
  simp only [fullSsaCcTrans, produced, wordStraightFragment, moveShape]
  exact bodyStraight

/-- Three-to-two output of an instruction stays in the straight-line grammar. -/
theorem threeToTwoInstStraight (instruction : WordLangInst (BitVec 64)) :
    wordStraightFragment (threeToTwoReg (.inst instruction)) = true := by
  cases instruction with
  | arith operation => cases operation <;> simp [threeToTwoReg, wordStraightFragment]
  | _ => simp [threeToTwoReg, wordStraightFragment]

theorem threeToTwoStraightFragment (p : WordLangProgHOL (BitVec 64))
    (supported : wordStraightFragment p = true) :
    wordStraightFragment (threeToTwoReg p) = true := by
  cases p <;> simp only [wordStraightFragment, Bool.and_eq_true] at supported
  all_goals try contradiction
  case skip => simp [threeToTwoReg, wordStraightFragment]
  case move priority moves => simp [threeToTwoReg, wordStraightFragment]
  case get destination store => simp [threeToTwoReg, wordStraightFragment]
  case opCurrHeap operator destination source => simp [threeToTwoReg, wordStraightFragment]
  case inst instruction => exact threeToTwoInstStraight instruction
  case seq first second =>
    have firstStraight := threeToTwoStraightFragment first supported.1
    have secondStraight := threeToTwoStraightFragment second supported.2
    simp [threeToTwoReg, wordStraightFragment, firstStraight, secondStraight]
termination_by sizeOf p
decreasing_by all_goals (subst_vars; simp_wf; try omega)

theorem threeToTwoRegProgStraightFragment (enabled : Bool)
    (p : WordLangProgHOL (BitVec 64)) (supported : wordStraightFragment p = true) :
    wordStraightFragment (threeToTwoRegProg enabled p) = true := by
  cases enabled
  · simpa [threeToTwoRegProg] using supported
  · simpa [threeToTwoRegProg] using threeToTwoStraightFragment p supported

theorem applyColourStraightFragment (f : Nat → Nat) (p : WordLangProgHOL (BitVec 64))
    (supported : wordStraightFragment p = true) :
    wordStraightFragment (applyColour f p) = true := by
  cases p <;> simp only [wordStraightFragment, Bool.and_eq_true] at supported
  all_goals try contradiction
  case skip => simp [applyColour, wordStraightFragment]
  case move priority moves => simp [applyColour, wordStraightFragment]
  case get destination store => simp [applyColour, wordStraightFragment]
  case opCurrHeap operator destination source => simp [applyColour, wordStraightFragment]
  case inst instruction => simp [applyColour, wordStraightFragment]
  case seq first second =>
    have firstStraight := applyColourStraightFragment f first supported.1
    have secondStraight := applyColourStraightFragment f second supported.2
    simp [applyColour, wordStraightFragment, firstStraight, secondStraight]
termination_by sizeOf p
decreasing_by all_goals (subst_vars; simp_wf; try omega)

/-- An accepted oracle colouring is an `applyColour` image. -/
theorem oracleColourOk_applyColour (k : Nat) (colour : Option (Spt Nat))
    (tree : Flapjack.RegAlloc.ClashTree) (program : WordLangProgHOL (BitVec 64))
    (forced : List (Nat × Nat)) {result : WordLangProgHOL (BitVec 64)}
    (accepted : oracleColourOk k colour tree program forced = some result) :
    ∃ f : Nat → Nat, result = applyColour f program := by
  unfold oracleColourOk at accepted
  dsimp only at accepted
  split at accepted
  · simp at accepted
  · split at accepted
    · split at accepted
      · injection accepted with same
        exact ⟨_, same.symm⟩
      · simp at accepted
    · simp at accepted

theorem wordAllocStraightFragment (fc : Nat)
    (config : Flapjack.Compiler.Encoders.Asm.AsmConfigExact 64)
    (algorithm limit : Nat) (program : WordLangProgHOL (BitVec 64))
    (colour : Option (Spt Nat)) (supported : wordStraightFragment program = true) :
    wordStraightFragment (wordAlloc fc config algorithm limit program colour) = true := by
  unfold wordAlloc
  cases accepted : oracleColourOk limit colour (getClashTree program []) program
      (getForced config program []) with
  | some coloured =>
    simp only [accepted]
    obtain ⟨f, same⟩ := oracleColourOk_applyColour limit colour (getClashTree program []) program
      (getForced config program []) accepted
    rw [same]
    exact applyColourStraightFragment f program supported
  | none =>
    simp only [accepted]
    split
    · exact applyColourStraightFragment _ program supported
    · exact supported

/-- Executed selected-path work of the composed pass result is bounded by the
same local budget, for any actual run state. -/
theorem compiled_fragment_executed {C F : Type} (count : Nat)
    (config : Flapjack.Compiler.Encoders.Asm.AsmConfigExact 64)
    (fc algorithm limit : Nat) (enabled : Bool)
    (p : WordLangProgHOL (BitVec 64)) (supported : selectionStraightLine p = true)
    (colour : Option (Spt Nat)) (source : WordSemStateFiniteExact 64 C F) :
    wordPathWork (wordAlloc fc config algorithm limit
      (threeToTwoRegProg enabled (fullSsaCcTrans count p)) colour) source ≤
      wordNodeCost p + (2 + count) + ssaStraightOverhead p + 3 * threeToTwoSites p := by
  have ssaStraight := fullSsaStraightFragment count p supported
  have threeStraight := threeToTwoRegProgStraightFragment enabled
    (fullSsaCcTrans count p) ssaStraight
  have allocStraight := wordAllocStraightFragment fc config algorithm limit
    (threeToTwoRegProg enabled (fullSsaCcTrans count p)) colour threeStraight
  have executed := wordPathWork_le_nodeCost_straight
    (wordAlloc fc config algorithm limit
      (threeToTwoRegProg enabled (fullSsaCcTrans count p)) colour) source allocStraight
  have static := compiled_fragment_nodeCost count config fc algorithm limit enabled
    p supported colour
  omega

#print axioms compiled_fragment_executed
#print axioms wordAllocStraightFragment
#print axioms ssaStraightFragment
#print axioms wordPathWork_le_nodeCost_straight
end InitECandidate.Runtime.FineCost
