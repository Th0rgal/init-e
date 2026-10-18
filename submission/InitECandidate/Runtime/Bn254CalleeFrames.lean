import InitECandidate.Runtime.GuardedGlobalsFrame
import InitECandidate.Runtime.Bn254AccelInitSource
import InitECandidate.Runtime.AllocationInitializersBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem originalGlobalsFrame_primitive (name : MlS) (operator : PrimOp) (arguments : List (ExpHOL 64)) :
    OriginalGlobalsFrame (.primitive name operator arguments) := by
  intro F state _
  rw [evaluateHOLFiniteState_primitive]
  repeat' first | split | rfl

/-- The accelerator is installed: its parameter block pointer is a nonzero word. -/
def Bn254AccelInstalled (globals : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  ∃ pointer : BitVec 64, globals.lookup (ofString "bn_accel_params") = some (.val (.word pointer)) ∧ pointer ≠ 0

/-- An installed accelerator makes bn254_accel_init return 0 at once. -/
theorem evaluate_bn254AccelInit_body_installed {F : Type} (state : PanSemStateFiniteExact 64 F)
    (installed : Bn254AccelInstalled state.globals) :
    evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_bn254_accel_init) =
      (some (.returned (.val (.word 0))),emptyLocalsHOLFinite state) := by
  obtain ⟨pointer,lookup,nonzero⟩ := installed
  have condition : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
      (.cmp .notEqual (.var .global (ofString "bn_accel_params")) (.const 0)) = some (.val (.word 1)) := by
    simp [evalHOLExact,lookup,Compiler.Encoders.Asm.wordCmpHOL]
    simpa using nonzero
  rw [source_bn254AccelInit_body,evaluateHOLFiniteState_seq_line780]
  simp only [evaluateHOLFiniteState_ite,condition]
  simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]

theorem bn254AccelInit_body_frame :
    GuardedGlobalsFrame Bn254AccelInstalled (sourceFunctionBody Guest.guestFn_bn254_accel_init) := by
  intro F state _ installed
  rw [evaluate_bn254AccelInit_body_installed state installed]
  rfl

/-- Structural search over globals-frame composition rules. -/
macro "orig_frame_search" : tactic => `(tactic| repeat first
    | exact originalGlobalsFrame_leaf _ (fun _ => rfl)
    | exact originalGlobalsFrame_primitive _ _ _
    | exact originalGlobalsFrame_external _ _ _ _ _
    | apply originalGlobalsFrame_sequence
    | apply originalGlobalsFrame_declaration
    | apply originalGlobalsFrame_conditional)

theorem u256IsZero_body_frame : OriginalGlobalsFrame (sourceFunctionBody Guest.guestFn_u256_is_zero) := by
  rw [sourceFunctionBody_eq_structural]; orig_frame_search

theorem u256Sub_body_frame : OriginalGlobalsFrame (sourceFunctionBody Guest.guestFn_u256_sub) := by
  rw [sourceFunctionBody_eq_structural]; orig_frame_search

theorem bn254AccelModmul_body_frame :
    GuardedGlobalsFrame Bn254AccelInstalled (sourceFunctionBody Guest.guestFn_bn254_accel_modmul) := by
  rw [sourceFunctionBody_eq_structural]
  apply GuardedGlobalsFrame.seq
  · exact GuardedGlobalsFrame.call _ (Or.inr rfl) _ _ _ _ originalRuntimeCode_bn254AccelInit_lookup
      bn254AccelInit_body_frame _
  · apply GuardedGlobalsFrame.of_original
    orig_frame_search

theorem fqMul_body_frame :
    GuardedGlobalsFrame Bn254AccelInstalled (sourceFunctionBody Guest.guestFn_fq_mul) := by
  rw [sourceFunctionBody_eq_structural]
  exact GuardedGlobalsFrame.call _ (Or.inl rfl) _ _ _ _ originalRuntimeCode_bn254AccelModmul_lookup
    bn254AccelModmul_body_frame _

theorem fqNeg_body_frame :
    GuardedGlobalsFrame Bn254AccelInstalled (sourceFunctionBody Guest.guestFn_fq_neg) := by
  rw [sourceFunctionBody_eq_structural]
  apply GuardedGlobalsFrame.decCall _ _ _ _ originalRuntimeCode_u256IsZero_lookup
    (GuardedGlobalsFrame.of_original u256IsZero_body_frame)
  apply GuardedGlobalsFrame.seq
  · apply GuardedGlobalsFrame.of_original
    orig_frame_search
  · exact GuardedGlobalsFrame.call _ (Or.inl rfl) _ _ _ _ originalRuntimeCode_u256Sub_lookup
      (GuardedGlobalsFrame.of_original u256Sub_body_frame) _

#print axioms bn254AccelModmul_body_frame
#print axioms fqMul_body_frame
#print axioms fqNeg_body_frame
end InitECandidate.Runtime
