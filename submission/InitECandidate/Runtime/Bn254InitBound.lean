import InitECandidate.Runtime.ProgBounded
import InitECandidate.Runtime.OriginalBn254InitCode
import InitECandidate.Runtime.AllocationInitializersBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Structural bound search over straight code, conditionals, declarations,
allocations and the given bounded callees. -/
syntax "pb_search" "[" term,* "]" : tactic
macro_rules
  | `(tactic| pb_search [$fs,*]) => `(tactic| repeat first
      | exact ProgBounded.straight _ (by decide)
      | apply ProgBounded.seq
      | apply ProgBounded.ite
      | apply ProgBounded.dec
      | exact ProgBounded.alloc _ _
      $[| exact ProgBounded.call $fs _ _]*
      $[| exact ProgBounded.tail $fs _]*
      $[| apply ProgBounded.decCall $fs]*)

theorem u256IsZero_funBounded : FunBounded (ofString "u256_is_zero") 0 :=
  ⟨_,_,_,originalRuntimeCode_u256IsZero_lookup,by
    rw [sourceFunctionBody_eq_structural]; exact ProgBounded.straight _ (by decide)⟩

theorem u256Sub_funBounded : FunBounded (ofString "u256_sub") 0 :=
  ⟨_,_,_,originalRuntimeCode_u256Sub_lookup,by
    rw [sourceFunctionBody_eq_structural]; exact ProgBounded.straight _ (by decide)⟩

theorem bn254AccelInit_funBounded : FunBounded (ofString "bn254_accel_init") 6 :=
  ⟨_,_,_,originalRuntimeCode_bn254AccelInit_lookup,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · pb_search []
    · decide⟩

theorem bn254AccelModmul_funBounded : FunBounded (ofString "bn254_accel_modmul") 7 :=
  ⟨_,_,_,originalRuntimeCode_bn254AccelModmul_lookup,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · pb_search [bn254AccelInit_funBounded]
    · decide⟩

theorem fqMul_funBounded : FunBounded (ofString "fq_mul") 8 :=
  ⟨_,_,_,originalRuntimeCode_fqMul_lookup,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · pb_search [bn254AccelModmul_funBounded]
    · decide⟩

theorem fqNeg_funBounded : FunBounded (ofString "fq_neg") 2 :=
  ⟨_,_,_,originalRuntimeCode_fqNeg_lookup,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · pb_search [u256IsZero_funBounded,u256Sub_funBounded]
    · decide⟩

theorem bn254Init_funBounded : FunBounded (ofString "bn254_init") 34 :=
  ⟨_,_,_,originalRuntimeCode_bn254Init_lookup,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · pb_search [bn254AccelInit_funBounded,fqMul_funBounded,fqNeg_funBounded]
    · decide⟩

/-- Every evaluation of the original bn254_init body costs at most 34 ticks
and never times out: already initialized, malformed globals, allocation
failure, inaccessible stores, accelerator FFI final or error outcomes, and
the successful first initialization. -/
theorem evaluate_bn254Init_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (budget : 34 ≤ state.clock) :
    let result := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_bn254_init)
    state.clock ≤ result.2.clock + 34 ∧ result.2.clock ≤ state.clock ∧ result.1 ≠ some .timeOut := by
  obtain ⟨_,body,_,lookup,bounded⟩ := bn254Init_funBounded
  have same : body = sourceFunctionBody Guest.guestFn_bn254_init := by
    rw [originalRuntimeCode_bn254Init_lookup] at lookup
    exact (Prod.mk.inj (Prod.mk.inj (Option.some.inj lookup)).2).1.symm
  subst same
  exact bounded state code budget

/-- The actual call `bn254_init()` costs at most 35 ticks in every outcome. -/
theorem evaluate_bn254Init_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (code : state.code = originalRuntimeCode) (budget : 35 ≤ state.clock) :
    let result := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "bn254_init") arguments)
    state.clock ≤ result.2.clock + 35 ∧ result.2.clock ≤ state.clock ∧ result.1 ≠ some .timeOut :=
  bn254Init_funBounded.call_bounded state destination arguments code budget

#print axioms evaluate_bn254Init_body_bounded
#print axioms evaluate_bn254Init_call_bounded
end InitECandidate.Runtime
