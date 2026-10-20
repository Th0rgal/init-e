import InitECandidate.Runtime.StackAddressCost
import InitECandidate.Runtime.StackPathWorkCorrect
import Flapjack.Compiler.Backend.StackRemove.Comp
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackRemove

/-- Local removal cost uses each actual frame offset rather than a global
bitmap/code-size scale. Only certified straight-line programs use this bound. -/
def stackRemovalUnits {width : Nat} [NeZero width]
    (bounds : BitVec width × BitVec width) : HolProg width → Nat
  | .seq first second => stackRemovalUnits bounds first + stackRemovalUnits bounds second
  | .stackStore _ slots =>
      if asmOffsetOkExact 0 bounds (wordOffset slots) then 1 else 2 * addressChunks slots + 1
  | .stackLoad _ slots =>
      if asmOffsetOkExact 0 bounds (wordOffset slots) then 1 else addressChunks slots + 2
  | _ => 1

theorem stack_removal_fragment {width : Nat} [NeZero width]
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (p : HolProg width) (supported : stackStraightLine p = true) :
    stackStraightLine (comp jump bounds pointer p) = true ∧
    stackLeaves (comp jump bounds pointer p) ≤ stackRemovalUnits bounds p := by
  cases p <;> simp only [stackStraightLine, Bool.and_eq_true] at supported
  all_goals try contradiction
  case skip => simp [comp, stackStraightLine, stackLeaves, stackRemovalUnits]
  case inst instruction => simp [comp, stackStraightLine, stackLeaves, stackRemovalUnits]
  case opCurrHeap operator destination src =>
    simp [comp, stackStraightLine, stackLeaves, stackRemovalUnits]
  case get destination name =>
    simp only [comp]
    split <;> simp [moveInst, moveHOL, stackStraightLine, stackLeaves, stackRemovalUnits]
  case stackStore register slots =>
    simp only [comp, stackRemovalUnits]
    split
    · simp [stackStraightLine, stackLeaves]
    · exact stack_store_address_fragment pointer register slots
  case stackLoad register slots =>
    simp only [comp, stackRemovalUnits]
    split
    · simp [stackStraightLine, stackLeaves]
    · have fragment := stack_load_address_fragment (width := width) register slots
      constructor
      · simpa only [stackStraightLine, moveInst, moveHOL, Bool.true_and] using fragment.1
      · simp only [stackLeaves, moveInst, moveHOL, stackRemovalUnits]
        omega
  case seq first second =>
    have firstBound := stack_removal_fragment jump bounds pointer first supported.1
    have secondBound := stack_removal_fragment jump bounds pointer second supported.2
    constructor
    · simpa only [comp, stackStraightLine, Bool.and_eq_true] using And.intro firstBound.1 secondBound.1
    · simp only [comp, stackLeaves, stackRemovalUnits]
      omega
termination_by sizeOf p

/-- Actual post-removal path budget with size-dependent address expansion. -/
theorem removed_straight_path_bound {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (p : HolProg width) (supported : stackStraightLine p = true)
    (source : StackSemStateFiniteExact width C F) :
    StackToLab.pathWork (comp jump bounds pointer p) source + 2 ≤ 4 * stackRemovalUnits bounds p := by
  have fragment := stack_removal_fragment jump bounds pointer p supported
  have pathBound := stack_straight_path_bound _ source fragment.1
  omega

/-- Retains all original flattening relation and result premises. -/
theorem removed_straight_flatten_bound {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (p : HolProg width) (supported : stackStraightLine p = true)
    (source : StackSemStateFiniteExact width C F) :
    StackToLab.BoundedFlattenProp (comp jump bounds pointer p) source
      (4 * stackRemovalUnits bounds p) := by
  apply StackToLab.boundedFlattenProp_mono
    (a := StackToLab.pathWork (comp jump bounds pointer p) source)
  · have bound := removed_straight_path_bound jump bounds pointer p supported source
    omega
  · exact StackToLab.pathWork_correct _ source

#print axioms removed_straight_flatten_bound
#print axioms removed_straight_path_bound
end InitECandidate.Runtime.FineCost
