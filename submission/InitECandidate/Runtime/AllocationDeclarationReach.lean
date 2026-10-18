import InitECandidate.Runtime.AllocationBodyBound
import InitECandidate.Runtime.AllocationCall
import InitECandidate.Runtime.AllocationFailureDeclarationNoReturn
import InitECandidate.Runtime.AllocationFailureDeclarationNoTimeout
import InitECandidate.Runtime.StatelessReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def AllocationDeclarationReady {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (pointer size : BitVec 64) (ready : PanSemStateFiniteExact 64 F) : Prop :=
  ready.locals = state.locals.update (name,.val (.word pointer)) ∧
    ready.memory = state.memory ∧ ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧
    ready.globals = (setGlobalHOLFinite (ofString "heap_ptr")
      (.val (.word (allocationEnd pointer size))) state).globals ∧
    (allocationEnd pointer size).toNat ≤ 33806089496 ∧
    pointer.toNat + size.toNat ≤ (allocationEnd pointer size).toNat ∧
    (allocationEnd pointer size).toNat % 8 = 0

/-- An allocation declaration reaches its actual continuation or terminates
through the original allocator trap; no successful-reserve premise is needed. -/
theorem evaluate_allocation_declaration_reaches {F : Type}
    (state : PanSemStateFiniteExact 64 F) (argument : ExpHOL 64)
    (name : MlS) (pointer size : BitVec 64) (continuation : ProgHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) [argument] = some [.val (.word size)])
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496) (budget : 2 ≤ state.clock) :
    Reaches state (.decCall name .one (ofString "alloc") [argument] continuation)
      (AllocationDeclarationReady state name pointer size) 2 continuation := by
  by_cases request : size ≤ (33806089496 : BitVec 64) - pointer
  · have within := allocationEnd_within_heap pointer size pointerBound request
    have covers := allocationEnd_covers pointer size
      (allocationGuard_sum_bound pointer size pointerBound request)
    obtain ⟨allocated,_,clock,memory,locals,installed,domain,_,_,globals,declaration⟩ :=
      evaluate_alloc_call_and_declaration state argument pointer size arguments code (by omega)
        heap request within
    let ready := setVarHOLFinite name (.val (.word pointer)) allocated
    left
    refine ⟨ready,⟨?_,memory,installed,domain,globals,within,covers.1,covers.2.2⟩,?_,?_,?_⟩
    · change allocated.locals.update _ = _
      rw [locals]
    · change state.clock ≤ allocated.clock + 2
      omega
    · change allocated.clock ≤ state.clock
      omega
    · rw [declaration name continuation]
      exact scoped_restore (evaluateHOLFiniteState ready continuation) _
  · have rejected : ((33806089496 : BitVec 64) - pointer).toNat < size.toNat := by
      have notLe : ¬ size.toNat ≤ ((33806089496 : BitVec 64) - pointer).toNat :=
        fun le => request (BitVec.le_def.mpr le)
      omega
    have terminal := evaluate_alloc_request_failure_declaration state argument pointer size name .one continuation
      arguments code heap rejected
    have noReturn := fun value => evaluate_alloc_request_failure_declaration_no_return state argument pointer size
      name .one continuation value arguments code heap rejected
    have noTimeout := evaluate_alloc_request_failure_declaration_no_timeout state argument pointer size
      name .one continuation arguments code heap rejected budget
    right
    cases run : evaluateHOLFiniteState state (.decCall name .one (ofString "alloc") [argument] continuation) with
    | mk result post =>
      rw [run] at terminal noReturn noTimeout
      dsimp only at terminal noReturn noTimeout
      cases result with
      | none => exact False.elim (terminal.1 rfl)
      | some result =>
        have ticks : post.clock = state.clock - 2 := terminal.2
        exact ⟨result,rfl,(by intro value equal; exact noReturn value (congrArg some equal)),
          (by change state.clock ≤ post.clock + 2; omega),
          (by change post.clock ≤ state.clock; omega),
          (by intro _ equal; exact noTimeout (congrArg some equal))⟩

#print axioms evaluate_allocation_declaration_reaches
end InitECandidate.Runtime
