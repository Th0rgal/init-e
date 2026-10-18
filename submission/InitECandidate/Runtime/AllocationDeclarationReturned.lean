import InitECandidate.Runtime.AllocationReturnedGuard
import InitECandidate.Runtime.AllocationBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Recover the real continuation of a successful allocator declaration. The
allocation guard follows from the returned execution, rather than a reserve
assumed in advance. -/
theorem allocation_declaration_returned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (argument : ExpHOL 64) (continuation : ProgHOL 64)
    (pointer size : BitVec 64) (value : ValueHOL 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [argument] = some [.val (.word size)])
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (bounded : pointer.toNat ≤ 33806089496)
    (run : evaluateHOLFiniteState state (.decCall name .one (ofString "alloc") [argument] continuation) =
      (some (.returned value),post)) :
    ∃ (ready output : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState ready continuation = (some (.returned value),output) ∧
      ready.locals = state.locals.update (name,.val (.word pointer)) ∧
      ready.memory = state.memory ∧ ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧
      ready.globals = (setGlobalHOLFinite (ofString "heap_ptr")
        (.val (.word (allocationEnd pointer size))) state).globals ∧
      (allocationEnd pointer size).toNat ≤ 33806089496 ∧
      pointer.toNat + size.toNat ≤ (allocationEnd pointer size).toNat ∧
      (allocationEnd pointer size).toNat % 8 = 0 ∧
      post.memory = output.memory ∧ post.globals = output.globals ∧ post.memaddrs = output.memaddrs := by
  have request := alloc_declaration_returned_request state post argument pointer size name .one continuation value args code heap run
  have ticks : state.clock ≠ 0 := by
    intro zero
    rw [evaluateHOLFiniteState_decCall_total,args] at run
    simp [zero] at run
    split at run <;> simp at run
  have within := allocationEnd_within_heap pointer size bounded request
  have rounded := allocationEnd_covers pointer size (allocationGuard_sum_bound pointer size bounded request)
  obtain ⟨allocated,_,_,memory,locals,installed,domain,_,_,globals,declaration⟩ :=
    evaluate_alloc_call_and_declaration state argument pointer size args code ticks heap request within
  rw [declaration name continuation] at run
  dsimp only at run
  let ready := setVarHOLFinite name (.val (.word pointer)) allocated
  change (let output := evaluateHOLFiniteState ready continuation;
    (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name)})) =
      (some (.returned value),post) at run
  cases tail : evaluateHOLFiniteState ready continuation with
  | mk result output =>
    rw [tail] at run
    have resultEq := (Prod.mk.inj run).1
    change result = some (.returned value) at resultEq
    subst result
    have restored := (Prod.mk.inj run).2
    refine ⟨ready,output,tail,?_,memory,installed,domain,globals,within,rounded.1,rounded.2.2,?_,?_,?_⟩
    · change allocated.locals.update _ = _
      rw [locals]
    all_goals rw [← restored]

#print axioms allocation_declaration_returned
end InitECandidate.Runtime
