import InitECandidate.Runtime.AllocCostExecuted
import InitECandidate.Runtime.WordSelectionNativeCost
import InitECandidate.Runtime.WordNativeParallelMoveCost
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.WordAlloc
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordToStackRegFormat
open Flapjack.Compiler.Backend.WordAlloc
open Flapjack.Compiler.Backend.WordInst
open Flapjack.Compiler.Encoders.Asm
theorem allocated_native_fragment (config : AsmConfigExact 64) (perf : Bool)
    (p : WordLangProgHOL (BitVec 64)) (bs : AppList (BitVec 64) × Nat)
    (kf : Nat × Nat × Nat) (supported : wordStraightFragment p = true) :
    stackStraightLine (compNative config perf p bs kf).1 = true ∧
    stackLeaves (compNative config perf p bs kf).1 ≤ 4 * wordNodeCost p := by
  cases p <;> simp only [wordStraightFragment, Bool.and_eq_true, decide_eq_true_eq] at supported
  all_goals try contradiction
  case skip => simp [compNative, stackStraightLine, stackLeaves, wordNodeCost]
  case inst instruction =>
    simpa only [compNative, wordNodeCost] using
      And.intro (native_instruction_straight (HolInst.ofWordLangInst instruction) kf)
        (native_instruction_leaves (HolInst.ofWordLangInst instruction) kf)
  case move priority moves =>
    simp only [compNative, wordNodeCost]
    refine ⟨native_parallel_move_straight moves kf, ?_⟩
    have bound := native_parallel_move_leaves (width := 64) moves kf
    omega
  case get destination name =>
    constructor
    · simp only [compNative]
      apply native_write_straight
      intro n
      rfl
    · simp only [compNative, wordNodeCost]
      apply Nat.le_trans (native_write_leaves _ _ kf (by intro n; rfl))
      omega
  case opCurrHeap operator destination src =>
    constructor
    · simp only [compNative]
      apply native_load_straight
      apply native_write_straight
      intro n
      rfl
    · simp only [compNative, native_load_leaves, wordNodeCost]
      apply Nat.le_trans (Nat.add_le_add (first_register_load_count _ kf)
        (native_write_leaves _ _ kf (by intro n; rfl)))
      omega
  case seq first second =>
    have firstBound := allocated_native_fragment config perf first bs kf supported.1
    have secondBound := allocated_native_fragment config perf second
      (compNative config perf first bs kf).2 kf supported.2
    constructor
    · simpa only [compNative, stackStraightLine, Bool.and_eq_true] using
        And.intro firstBound.1 secondBound.1
    · simp only [compNative, stackLeaves, wordNodeCost]
      omega
termination_by sizeOf p

/-- Full fragment path through SSA, register rewriting, allocation and native
Stack lowering, including arbitrary parallel moves and worst-case spills.
The remaining deleting passes and recursive Word control composition are separate. -/
theorem compiled_fragment_native_path_bound {C F : Type} (count : Nat)
    (config : AsmConfigExact 64) (perf : Bool) (fc algorithm limit : Nat) (enabled : Bool)
    (p : WordLangProgHOL (BitVec 64)) (supported : selectionStraightLine p = true)
    (colour : Option (Spt Nat)) (bs : AppList (BitVec 64) × Nat) (kf : Nat × Nat × Nat)
    (source : StackSemStateFiniteExact 64 C F) :
    StackToLab.pathWork (compNative config perf
      (wordAlloc fc config algorithm limit
        (threeToTwoRegProg enabled (fullSsaCcTrans count p)) colour) bs kf).1 source ≤
      16 * (wordNodeCost p + (2 + count) + ssaStraightOverhead p + 3 * threeToTwoSites p) := by
  have grammar := wordAllocStraightFragment fc config algorithm limit
    (threeToTwoRegProg enabled (fullSsaCcTrans count p)) colour
    (threeToTwoRegProgStraightFragment enabled _ (fullSsaStraightFragment count p supported))
  have native := allocated_native_fragment config perf _ bs kf grammar
  have path := stack_straight_path_bound _ source native.1
  have bound := compiled_fragment_nodeCost count config fc algorithm limit enabled p supported colour
  omega

#print axioms compiled_fragment_native_path_bound
#print axioms allocated_native_fragment
end InitECandidate.Runtime.FineCost
