import InitECandidate.Runtime.WitnessPhysicalStack
import InitECandidate.Runtime.WitnessTraversalChildCredit
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The actual record's stage and index remain readable as child credit under
an old-arena frame, including the resolver's allowed current hash-field write. -/
theorem witness_stack_child_credit_after_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (input inputLength frontier top : BitVec 64) (persistentFloor lower : Nat)
    (stack : WitnessPhysicalStack s input inputLength frontier persistentFloor lower top)
    (floorBeforeHeap : persistentFloor≤frontier.toNat)
    (memory : ∀ watched : BitVec 64, lower≤watched.toNat → watched.toNat<frontier.toNat → watched≠top+80 →
      post.memory watched=s.memory watched) :
    witnessTraversalChildCredit post top=witnessTraversalChildCredit s top := by
  cases stack with
  | nil => simp [witnessTraversalChildCredit]
  | cons above valid ordered tail =>
    have before := valid.2.1
    have address (offset : Nat) (inside : offset<88) : (top+BitVec.ofNat 64 offset).toNat=top.toNat+offset := by
      have bound := frontier.isLt
      rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show offset<2^64 by omega)]
      exact Nat.mod_eq_of_lt (by omega)
    have field (offset : Nat) (inside : offset<88) (notHash : offset≠80) :
        post.memory (top+BitVec.ofNat 64 offset)=s.memory (top+BitVec.ofNat 64 offset) := by
      apply memory
      · rw [address offset inside]; omega
      · rw [address offset inside]; omega
      · intro same
        have equal := congrArg BitVec.toNat same
        change (top+BitVec.ofNat 64 offset).toNat=(top+BitVec.ofNat 64 80).toNat at equal
        rw [address offset inside,address 80 (by decide)] at equal
        omega
    exact witnessTraversalChildCredit_after_frame s post top
      (by simpa using field 8 (by decide) (by decide)) (by simpa using field 32 (by decide) (by decide))

#print axioms witness_stack_child_credit_after_frame
end InitECandidate.Runtime
