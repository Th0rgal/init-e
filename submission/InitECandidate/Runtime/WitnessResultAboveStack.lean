import InitECandidate.Runtime.WitnessAllocationStackFrame
import InitECandidate.Runtime.CompletedNodeEnvelope
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A nonzero delivered result lies beyond a frontier containing every live
parent table. The saved frontier need not equal the moving current heap. -/
def WitnessResultAboveStack {F : Type} (s : PanSemStateFiniteExact 64 F)
    (input inputLength top node : BitVec 64) (persistentFloor lower : Nat) : Prop :=
  node=0 ∨ ∃ savedFrontier : BitVec 64, savedFrontier.toNat≤node.toNat ∧
    WitnessAllocationStack s input inputLength savedFrontier persistentFloor lower top

/-- Actual completed-node allocation bounds and a retained old stack suffice;
no claim is made that a global persistent floor alone bounds its slice tables. -/
theorem witness_result_above_stack_of_completed {F : Type} (s : PanSemStateFiniteExact 64 F)
    (input inputLength frontier top node : BitVec 64) (persistentFloor lower : Nat)
    (stack : WitnessAllocationStack s input inputLength frontier persistentFloor lower top)
    (envelope : CompletedNodeEnvelope s node frontier.toNat) :
    WitnessResultAboveStack s input inputLength top node persistentFloor lower := by
  rcases envelope with zero | ⟨heap,atHeap,above,extent,capped⟩
  · exact Or.inl zero
  · exact Or.inr ⟨frontier,above,stack⟩

/-- The actual branch pointer is above the saved frontier of its retained
parents. This gives the result-versus-parent-table invariant on branch pop. -/
theorem witness_branch_result_above_parents {F : Type} (s : PanSemStateFiniteExact 64 F)
    (input inputLength frontier top previous branch : BitVec 64) (persistentFloor lower : Nat)
    (stack : WitnessAllocationStack s input inputLength frontier persistentFloor lower top)
    (nonempty : top≠0) (link : s.memory top=.word previous)
    (stage : s.memory (top+8)=.word (2 : BitVec 64)) (atBranch : s.memory (top+16)=.word branch) :
    WitnessResultAboveStack s input inputLength previous branch persistentFloor lower := by
  obtain ⟨parent,_,above,tail⟩ := stack.branch_parent s input inputLength frontier top previous branch
    persistentFloor lower nonempty link stage atBranch
  exact Or.inr ⟨parent,above,tail⟩

/-- A nonempty retained stack places its record and real17-entry branch table
below any nonzero delivered result, as required by the concrete unwind bound. -/
theorem WitnessResultAboveStack.branch_geometry {F : Type} (s : PanSemStateFiniteExact 64 F)
    (input inputLength top node array : BitVec 64) (persistentFloor lower : Nat)
    (valid : WitnessResultAboveStack s input inputLength top node persistentFloor lower)
    (nonempty : top≠0) (stage : s.memory (top+8)=.word (2 : BitVec 64))
    (atArray : s.memory (top+24)=.word array) :
    node=0 ∨ (top.toNat+88≤node.toNat ∧ array.toNat+272≤node.toNat) := by
  rcases valid with zero | ⟨savedFrontier,above,stack⟩
  · exact Or.inl zero
  · cases stack with
    | nil => exact False.elim (nonempty rfl)
    | cons parent recordAbove record floorBound parentBound ordered branchAbove tail =>
      obtain ⟨positive,recordBefore,accessible,link,actual,count,kind,p,n,arity,atKind,arrayCell,
        atP,atN,tableAbove,tableEnd,table,nibs,branch⟩ := record
      have sameArray := HolWordLab.word.inj (arrayCell.symm.trans atArray)
      have sameStage : kind=2 := HolWordLab.word.inj (atKind.symm.trans stage)
      subst actual; subst kind
      have countEq : count=17 := by
        rcases arity with ⟨impossible,_⟩ | ⟨_,same⟩
        · cases impossible
        · exact same
      subst count
      exact Or.inr ⟨by omega,by simpa using tableEnd.trans above⟩

theorem WitnessResultAboveStack.record_geometry {F : Type} (s : PanSemStateFiniteExact 64 F)
    (input inputLength top node : BitVec 64) (persistentFloor lower : Nat)
    (valid : WitnessResultAboveStack s input inputLength top node persistentFloor lower)
    (nonempty : top≠0) : node=0 ∨ top.toNat+88≤node.toNat := by
  rcases valid with zero | ⟨savedFrontier,above,stack⟩
  · exact Or.inl zero
  · cases stack with
    | nil => exact False.elim (nonempty rfl)
    | cons parent recordAbove record floorBound parentBound ordered branchAbove tail =>
      have before := record.2.1
      exact Or.inr (by omega)

#print axioms witness_result_above_stack_of_completed
#print axioms witness_branch_result_above_parents
#print axioms WitnessResultAboveStack.branch_geometry
#print axioms WitnessResultAboveStack.record_geometry
end InitECandidate.Runtime
