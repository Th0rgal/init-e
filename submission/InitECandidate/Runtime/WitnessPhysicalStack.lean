import InitECandidate.Runtime.WitnessPhysicalRecordFrame
import InitECandidate.Runtime.DecodeWitnessTraversalMeasure
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The real saved-link chain, with each full record above the live scratch
frontier and strictly below its older parent. No abstract stack oracle is used. -/
inductive WitnessPhysicalStack {F : Type} (s : PanSemStateFiniteExact 64 F)
    (input inputLength frontier : BitVec 64) (persistentFloor lower : Nat) : BitVec 64 → Prop
  | nil : WitnessPhysicalStack s input inputLength frontier persistentFloor lower 0
  | cons {record previous : BitVec 64}
      (above : lower ≤ record.toNat)
      (valid : WitnessPhysicalRecord s record previous input inputLength frontier persistentFloor)
      (ordered : previous=0 ∨ record.toNat+88 ≤ previous.toNat)
      (tail : WitnessPhysicalStack s input inputLength frontier persistentFloor lower previous) :
      WitnessPhysicalStack s input inputLength frontier persistentFloor lower record

/-- A lower scratch frontier keeps every existing physical record live. -/
theorem WitnessPhysicalStack.lower {F : Type} (s : PanSemStateFiniteExact 64 F)
    (input inputLength frontier top : BitVec 64) (persistentFloor lower nextLower : Nat)
    (stack : WitnessPhysicalStack s input inputLength frontier persistentFloor lower top)
    (moves : nextLower≤lower) :
    WitnessPhysicalStack s input inputLength frontier persistentFloor nextLower top := by
  induction stack with
  | nil => exact .nil
  | cons above valid ordered tail ih => exact .cons (by omega) valid ordered ih

/-- Installing a fresh record below the old live scratch frontier establishes
both the concrete saved-link chain and its parent address ordering. -/
theorem WitnessPhysicalStack.push {F : Type} (s : PanSemStateFiniteExact 64 F)
    (input inputLength frontier record previous : BitVec 64) (persistentFloor lower nextLower : Nat)
    (stack : WitnessPhysicalStack s input inputLength frontier persistentFloor lower previous)
    (valid : WitnessPhysicalRecord s record previous input inputLength frontier persistentFloor)
    (fresh : record.toNat+88≤lower) (nextAbove : nextLower≤record.toNat) :
    WitnessPhysicalStack s input inputLength frontier persistentFloor nextLower record := by
  have moves : nextLower≤lower := by omega
  apply WitnessPhysicalStack.cons nextAbove valid
  · cases stack with
    | nil => exact Or.inl rfl
    | cons above parent ordered tail => exact Or.inr (by omega)
  · exact stack.lower s input inputLength frontier previous persistentFloor lower nextLower moves

/-- Concrete framed old memory retains the entire saved-link chain as the
heap grows and the scratch frontier moves down. -/
theorem WitnessPhysicalStack.after_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (input inputLength frontier nextFrontier top : BitVec 64) (persistentFloor lower nextLower : Nat)
    (stack : WitnessPhysicalStack s input inputLength frontier persistentFloor lower top)
    (floorBeforeHeap : persistentFloor ≤ frontier.toNat)
    (growth : frontier.toNat ≤ nextFrontier.toNat) (lowerMoves : nextLower ≤ lower)
    (domain : post.memaddrs=s.memaddrs)
    (memory : ∀ watched : BitVec 64, lower ≤ watched.toNat → watched.toNat<frontier.toNat →
      post.memory watched=s.memory watched) :
    WitnessPhysicalStack post input inputLength nextFrontier persistentFloor nextLower top := by
  induction stack with
  | nil => exact .nil
  | @cons record previous above valid ordered tail ih =>
    have framed := valid.after_frame s post record previous input inputLength frontier nextFrontier persistentFloor
      growth domain (by
        intro offset inside notOcc notHash
        have small : record.toNat+offset < 2^64 := by
          have bound := frontier.isLt
          have before := valid.2.1
          omega
        have address : (record+BitVec.ofNat 64 offset).toNat=record.toNat+offset := by
          rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show offset<2^64 by omega),Nat.mod_eq_of_lt small]
        apply memory
        · rw [address]; omega
        · rw [address]; have before := valid.2.1; omega)
      (by intro watched afterRecord beforeHeap; exact memory watched (by omega) beforeHeap)
    exact .cons (by omega) framed ordered ih

/-- Reading the actual nonempty top exposes its concrete saved parent and the
strict address ordering used by the arithmetic termination measure. -/
theorem WitnessPhysicalStack.parent {F : Type} (s : PanSemStateFiniteExact 64 F)
    (input inputLength frontier top previous : BitVec 64) (persistentFloor lower : Nat)
    (stack : WitnessPhysicalStack s input inputLength frontier persistentFloor lower top)
    (nonempty : top≠0) (link : s.memory top=.word previous) :
    (previous=0 ∨ top.toNat<previous.toNat) ∧
      WitnessPhysicalStack s input inputLength frontier persistentFloor lower previous := by
  cases stack with
  | nil => exact False.elim (nonempty rfl)
  | cons above valid ordered tail =>
    have same := HolWordLab.word.inj (valid.2.2.2.1.symm.trans link)
    subst previous
    refine ⟨?_,tail⟩
    rcases ordered with empty | later
    · exact Or.inl empty
    · exact Or.inr (by omega)

theorem WitnessPhysicalStack.pop_measure {F : Type} (s : PanSemStateFiniteExact 64 F)
    (input inputLength frontier top previous : BitVec 64) (persistentFloor lower capacity children nextChildren mode nextMode : Nat)
    (stack : WitnessPhysicalStack s input inputLength frontier persistentFloor lower top)
    (nonempty : top≠0) (link : s.memory top=.word previous)
    (childBound : nextChildren≤16) (modeBound : nextMode≤3) :
    decodeWitnessMeasure capacity previous nextChildren nextMode < decodeWitnessMeasure capacity top children mode :=
  decodeWitnessMeasure_pop capacity top previous children nextChildren mode nextMode nonempty
    (stack.parent s input inputLength frontier top previous persistentFloor lower nonempty link).1 childBound modeBound

#print axioms WitnessPhysicalStack.push
#print axioms WitnessPhysicalStack.after_frame
#print axioms WitnessPhysicalStack.parent
#print axioms WitnessPhysicalStack.pop_measure
end InitECandidate.Runtime
