import InitECandidate.Runtime.AllocCostSSA
import Flapjack.Compiler.Backend.WordInst
import Flapjack.Compiler.Backend.WordAlloc.WordAllocDef
import Flapjack.Compiler.Backend.WordAlloc.Colour
import Flapjack.Compiler.Backend.WordAlloc.OracleColour
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.WordAlloc Flapjack.WordAlloc
open Flapjack.Compiler.Backend.WordInst
open InitECandidate.Runtime.WordToStack

/-!
# Three-to-two and register-allocation work transfer

`threeToTwoReg` replaces one two-address instruction by a parallel move and a
one-address instruction.  The added work is exactly three local nodes per
rewritten instruction (one move word, its move node and the new `Seq`), measured
by `threeToTwoSites`.  `applyColour` only renames registers and keeps every
constructor and every parallel-move length; `wordAlloc` therefore never
increases the local Word node envelope.  Spill/reload work is not hidden here:
it belongs to the Stack/native lowering stage already covered by
`WordNativeInstructionCost`.
-/

/-- Instructions rewritten by `three_to_two_reg`. -/
def threeToTwoRewrites : WordLangInst (BitVec 64) → Bool
  | .arith (.binop _ _ _ _) => true
  | .arith (.shift _ _ _ _) => true
  | .arith (.addCarry _ _ _ _) => true
  | .arith (.addOverflow _ _ _ _) => true
  | .arith (.subOverflow _ _ _ _) => true
  | _ => false

/-- Rewritten instructions, including `OpCurrHeap`, over a program. -/
def threeToTwoSites : WordLangProgHOL (BitVec 64) → Nat
  | .inst i => if threeToTwoRewrites i then 1 else 0
  | .opCurrHeap _ _ _ => 1
  | .seq first second => threeToTwoSites first + threeToTwoSites second
  | .mustTerminate body => threeToTwoSites body
  | .ite _ _ _ thenBranch elseBranch =>
      threeToTwoSites thenBranch + threeToTwoSites elseBranch
  | .call none _ _ handler =>
      match handler with
      | none => 0
      | some (_, code, _, _) => threeToTwoSites code
  | .call (some (_, _, returnCode, _, _)) _ _ handler =>
      threeToTwoSites returnCode +
        match handler with
        | none => 0
        | some (_, code, _, _) => threeToTwoSites code
  | .loop _ body _ => threeToTwoSites body
  | _ => 0
termination_by p => sizeOf p

/-- Every rewrite adds one move word, one move node and one sequence node. -/
theorem threeToTwoReg_nodeCost (p : WordLangProgHOL (BitVec 64)) :
    wordNodeCost (threeToTwoReg p) ≤ wordNodeCost p + 3 * threeToTwoSites p := by
  cases p
  case skip => simp [threeToTwoReg, wordNodeCost, threeToTwoSites]
  case move priority moves => simp [threeToTwoReg, wordNodeCost, threeToTwoSites]
  case inst instruction =>
    cases instruction with
    | arith operation =>
      cases operation <;> simp [threeToTwoReg, threeToTwoRewrites, wordNodeCost, threeToTwoSites]
    | _ => simp [threeToTwoReg, threeToTwoRewrites, wordNodeCost, threeToTwoSites]
  case assign name value => simp [threeToTwoReg, wordNodeCost, threeToTwoSites]
  case get destination store => simp [threeToTwoReg, wordNodeCost, threeToTwoSites]
  case set store value => simp [threeToTwoReg, wordNodeCost, threeToTwoSites]
  case store address value => simp [threeToTwoReg, wordNodeCost, threeToTwoSites]
  case mustTerminate body =>
    have bound := threeToTwoReg_nodeCost body
    simp [threeToTwoReg, wordNodeCost, threeToTwoSites]
    omega
  case call returns target arguments handler =>
    cases returns with
    | none =>
      cases handler with
      | none => simp [threeToTwoReg, wordNodeCost, threeToTwoSites]
      | some handlerData =>
        rcases handlerData with ⟨reg, code, l1, l2⟩
        have bound := threeToTwoReg_nodeCost code
        simp [threeToTwoReg, wordNodeCost, threeToTwoSites]
        omega
    | some returnData =>
      rcases returnData with ⟨values, cutsets, returnCode, l1, l2⟩
      cases handler with
      | none =>
        have bound := threeToTwoReg_nodeCost returnCode
        simp [threeToTwoReg, wordNodeCost, threeToTwoSites]
        omega
      | some handlerData =>
        rcases handlerData with ⟨reg, code, l1', l2'⟩
        have returnBound := threeToTwoReg_nodeCost returnCode
        have handlerBound := threeToTwoReg_nodeCost code
        simp [threeToTwoReg, wordNodeCost, threeToTwoSites]
        omega
  case seq first second =>
    have firstBound := threeToTwoReg_nodeCost first
    have secondBound := threeToTwoReg_nodeCost second
    simp [threeToTwoReg, wordNodeCost, threeToTwoSites]
    omega
  case ite operator condition right thenBranch elseBranch =>
    have thenBound := threeToTwoReg_nodeCost thenBranch
    have elseBound := threeToTwoReg_nodeCost elseBranch
    simp [threeToTwoReg, wordNodeCost, threeToTwoSites]
    omega
  case loop liveIn body liveOut =>
    have bound := threeToTwoReg_nodeCost body
    simp [threeToTwoReg, wordNodeCost, threeToTwoSites]
    omega
  case alloc destination cutsets => simp [threeToTwoReg, wordNodeCost, threeToTwoSites]
  case storeConsts source bitmap codeLength dataLength constants =>
    simp [threeToTwoReg, wordNodeCost, threeToTwoSites]
  case raise exception => simp [threeToTwoReg, wordNodeCost, threeToTwoSites]
  case «return» label values => simp [threeToTwoReg, wordNodeCost, threeToTwoSites]
  case «break» label => simp [threeToTwoReg, wordNodeCost, threeToTwoSites]
  case «continue» label => simp [threeToTwoReg, wordNodeCost, threeToTwoSites]
  case tick => simp [threeToTwoReg, wordNodeCost, threeToTwoSites]
  case opCurrHeap operator destination source =>
    simp [threeToTwoReg, wordNodeCost, threeToTwoSites]
  case locValue destination source => simp [threeToTwoReg, wordNodeCost, threeToTwoSites]
  case install codeBuffer codeLength dataBuffer dataLength cutsets =>
    simp [threeToTwoReg, wordNodeCost, threeToTwoSites]
  case codeBufferWrite address value => simp [threeToTwoReg, wordNodeCost, threeToTwoSites]
  case dataBufferWrite address value => simp [threeToTwoReg, wordNodeCost, threeToTwoSites]
  case ffi function configuration configurationLength array arrayLength live =>
    simp [threeToTwoReg, wordNodeCost, threeToTwoSites]
  case shareInst operator name address => simp [threeToTwoReg, wordNodeCost, threeToTwoSites]
termination_by sizeOf p
decreasing_by all_goals (subst_vars; simp_wf; try omega)

/-- `threeToTwoRegProg` applies the rewrite only when the configuration asks. -/
theorem threeToTwoRegProg_nodeCost (enabled : Bool) (p : WordLangProgHOL (BitVec 64)) :
    wordNodeCost (threeToTwoRegProg enabled p) ≤ wordNodeCost p + 3 * threeToTwoSites p := by
  cases enabled
  · simp [threeToTwoRegProg]
  · simpa only [threeToTwoRegProg, if_true, Bool.false_eq_true] using threeToTwoReg_nodeCost p

/-- Register-renaming never changes a parallel-move length nor the constructor
shape, so the local node envelope is invariant. -/
theorem applyColour_nodeCost (f : Nat → Nat) (p : WordLangProgHOL (BitVec 64)) :
    wordNodeCost (applyColour f p) = wordNodeCost p := by
  cases p
  case skip => simp [applyColour, wordNodeCost]
  case move priority moves =>
    simp [applyColour, wordNodeCost, List.length_zip]
  case inst instruction => simp [applyColour, wordNodeCost]
  case assign name value => simp [applyColour, wordNodeCost]
  case get destination store => simp [applyColour, wordNodeCost]
  case set store value => simp [applyColour, wordNodeCost]
  case store address value => simp [applyColour, wordNodeCost]
  case mustTerminate body =>
    have bodyEq := applyColour_nodeCost f body
    simp [applyColour, wordNodeCost, bodyEq]
  case call returns target arguments handler =>
    cases returns with
    | none =>
      cases handler with
      | none => simp [applyColour, wordNodeCost]
      | some handlerData =>
        rcases handlerData with ⟨reg, code, l1, l2⟩
        have codeEq := applyColour_nodeCost f code
        simp [applyColour, wordNodeCost, codeEq]
    | some returnData =>
      rcases returnData with ⟨values, cutsets, returnCode, l1, l2⟩
      cases handler with
      | none =>
        have codeEq := applyColour_nodeCost f returnCode
        simp [applyColour, wordNodeCost, codeEq]
      | some handlerData =>
        rcases handlerData with ⟨reg, code, l1', l2'⟩
        have returnEq := applyColour_nodeCost f returnCode
        have handlerEq := applyColour_nodeCost f code
        simp [applyColour, wordNodeCost, returnEq, handlerEq]
  case seq first second =>
    have firstEq := applyColour_nodeCost f first
    have secondEq := applyColour_nodeCost f second
    simp [applyColour, wordNodeCost, firstEq, secondEq]
  case ite operator condition right thenBranch elseBranch =>
    have thenEq := applyColour_nodeCost f thenBranch
    have elseEq := applyColour_nodeCost f elseBranch
    simp [applyColour, wordNodeCost, thenEq, elseEq]
  case loop liveIn body liveOut =>
    have bodyEq := applyColour_nodeCost f body
    simp [applyColour, wordNodeCost, bodyEq]
  case alloc destination cutsets => simp [applyColour, wordNodeCost]
  case storeConsts source bitmap codeLength dataLength constants =>
    simp [applyColour, wordNodeCost]
  case raise exception => simp [applyColour, wordNodeCost]
  case «return» label values => simp [applyColour, wordNodeCost]
  case «break» label => simp [applyColour, wordNodeCost]
  case «continue» label => simp [applyColour, wordNodeCost]
  case tick => simp [applyColour, wordNodeCost]
  case opCurrHeap operator destination source => simp [applyColour, wordNodeCost]
  case locValue destination source => simp [applyColour, wordNodeCost]
  case install codeBuffer codeLength dataBuffer dataLength cutsets =>
    simp [applyColour, wordNodeCost]
  case codeBufferWrite address value => simp [applyColour, wordNodeCost]
  case dataBufferWrite address value => simp [applyColour, wordNodeCost]
  case ffi function configuration configurationLength array arrayLength live =>
    simp [applyColour, wordNodeCost]
  case shareInst operator name address => simp [applyColour, wordNodeCost]
termination_by sizeOf p
decreasing_by all_goals (subst_vars; simp_wf; try omega)

/-- An accepted oracle colouring is exactly an `applyColour` image. -/
theorem oracleColourOk_nodeCost (k : Nat) (colour : Option (Spt Nat))
    (tree : Flapjack.RegAlloc.ClashTree) (program : WordLangProgHOL (BitVec 64))
    (forced : List (Nat × Nat)) {result : WordLangProgHOL (BitVec 64)}
    (accepted : oracleColourOk k colour tree program forced = some result) :
    wordNodeCost result = wordNodeCost program := by
  unfold oracleColourOk at accepted
  dsimp only at accepted
  split at accepted
  · simp at accepted
  · split at accepted
    · split at accepted
      · injection accepted with same
        rw [← same]
        exact applyColour_nodeCost _ _
      · simp at accepted
    · simp at accepted

/-- The allocator either falls back to its input or applies a colouring; it
never inserts ordinary Word instructions. -/
theorem wordAlloc_nodeCost_le (fc : Nat) (config : Flapjack.Compiler.Encoders.Asm.AsmConfigExact 64)
    (algorithm limit : Nat) (program : WordLangProgHOL (BitVec 64))
    (colour : Option (Spt Nat)) :
    wordNodeCost (wordAlloc fc config algorithm limit program colour) ≤ wordNodeCost program := by
  unfold wordAlloc
  cases accepted : oracleColourOk limit colour (getClashTree program []) program
      (getForced config program []) with
  | some coloured =>
    simp only [accepted]
    rw [oracleColourOk_nodeCost limit colour (getClashTree program []) program
      (getForced config program []) accepted]
    exact Nat.le_refl _
  | none =>
    simp only [accepted]
    split
    · rw [applyColour_nodeCost _ _]
      exact Nat.le_refl _
    · exact Nat.le_refl _

#print axioms wordAlloc_nodeCost_le
#print axioms applyColour_nodeCost
#print axioms threeToTwoRegProg_nodeCost
#print axioms threeToTwoReg_nodeCost
end InitECandidate.Runtime.FineCost
