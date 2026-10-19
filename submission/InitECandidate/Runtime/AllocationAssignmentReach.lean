import InitECandidate.Runtime.AllocationAssignmentReturned
import InitECandidate.Runtime.AllocationFragmentBound
import InitECandidate.Runtime.NoDirectReturnWhile
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Assignment allocation reaches the real next statement or aborts within
its uniform bound, including allocation rejection and expression failures. -/
theorem evaluate_allocation_assignment_reaches {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (argument : ExpHOL 64) (pointer size : BitVec 64) (continuation : ProgHOL 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [argument] = some [.val (.word size)])
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (bounded : pointer.toNat ≤ 33806089496) (budget : 2 ≤ state.clock) :
    Reaches state (.seq (.call (some (some (.local,name),none)) (ofString "alloc") [argument]) continuation)
      (AllocationDeclarationReady state name pointer size) 2 continuation := by
  have bound := evaluate_alloc_uniform_call_bounded state (some (.local,name)) [argument] code budget
  apply reaches_seq
  cases run : evaluateHOLFiniteState state (.call (some (some (.local,name),none)) (ofString "alloc") [argument]) with
  | mk result post =>
    rw [run] at bound
    dsimp only at bound
    cases result with
    | none =>
      exact Or.inl ⟨post,allocation_assignment_normal state post name argument pointer size args code heap bounded run,
        bound.1,bound.2.1,rfl⟩
    | some stopped =>
      right
      refine ⟨stopped,rfl,?_,bound.1,bound.2.1,?_⟩
      · intro value equal
        have impossible := evaluate_noDirectReturnWhile
          (.call (some (some (.local,name),none)) (ofString "alloc") [argument]) (by rfl) state value
        rw [run] at impossible
        exact impossible (congrArg some equal)
      · intro _ equal
        exact bound.2.2 (congrArg some equal)

#print axioms evaluate_allocation_assignment_reaches
end InitECandidate.Runtime
