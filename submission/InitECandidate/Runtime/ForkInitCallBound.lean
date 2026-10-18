import InitECandidate.Runtime.ForkInitBodyBound
import InitECandidate.Runtime.OriginalForkInitCode
import InitECandidate.Runtime.PanUniformCalleeCallBound
import InitECandidate.Runtime.LookupCodeInstalledBody
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual calls to the original fork initializer, including failed argument
binding and all early outcomes, consume at most 516 source ticks. -/
theorem evaluate_forkInit_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (pointer oldZero oldPrecompile : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (zeroSlot : state.globals.lookup (ofString "zero32") = some (.val (.word oldZero)))
    (precompileSlot : state.globals.lookup (ofString "precompile_addrs") = some (.val (.word oldPrecompile)))
    (aligned : pointer.toNat % 8 = 0)
    (small : pointer.toNat + 392 ≤ 33806089496)
    (arena : ∀ address : BitVec 64, pointer.toNat ≤ address.toNat →
      address.toNat < pointer.toNat + 392 → state.memaddrs address)
    (budget : 516 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state
      (.call (some (destination,none)) (ofString "fork_init") arguments)
    state.clock ≤ evaluated.2.clock + 516 ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  apply evaluate_uniformCallee_call_bounded state (ofString "fork_init") destination arguments 515 budget
  intro values body locals returnShape found
  have same := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "fork_init") []
    (sourceFunctionBody Guest.guestFn_fork_init) body .one returnShape values locals
    (by rw [code]; exact originalRuntimeCode_forkInit_lookup) found
  subst same
  exact evaluate_forkInit_body_bounded (callEntryStateHOLFinite state locals) pointer oldZero oldPrecompile
    code heap zeroSlot precompileSlot aligned small arena (by change 515 ≤ state.clock - 1; omega)

#print axioms evaluate_forkInit_call_bounded
end InitECandidate.Runtime
