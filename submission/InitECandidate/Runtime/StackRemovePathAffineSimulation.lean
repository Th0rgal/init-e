import InitECandidate.Runtime.StackRemovePathWorkCorrect
import InitECandidate.Runtime.StackRemovePathAffine
namespace InitECandidate.Runtime.StackRemove
open Flapjack Compiler.Backend.StackLang StackSemEvaluate StackSemStateOps
open Flapjack.Compiler.Backend.StackRemove
open StackToLab

/-- Full original stack-removal compiler simulation with an extra target clock
affine in the source fuel: scale*((2L+2)*clock+2L), for bounded code and a fixed
bitmap table. All original relation, terminal FFI and outcome guarantees remain. -/
theorem compCorrect_affine {width : Nat} [NeZero width] {C F : Type}
    (limit scale : Nat) (program : HolProg width) (source : StackSemStateFiniteExact width C F)
    (sizeBound : sizeOf program ≤ limit) (code : CodeSizeState limit source)
    (bitmap : BitmapBudget scale source)
    (result : Option (StackSemResult width)) (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : evaluate (program, source) = (result, postSource) ∧ result ≠ some .error ∧
      stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound program pointer) :
    ∃ clock, clock ≤ scale * ((2 * limit + 2) * source.clock + 2 * limit) ∧ ∃ postTarget,
      evaluate (comp jump bounds pointer program, {target with clock := clock + target.clock}) =
        (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  obtain ⟨clock, bound, rest⟩ := removePathWork_correct program source result postSource target
    pointer bounds jump hypothesis
  exact ⟨clock, Nat.le_trans bound (removePathWork_affine_fuel limit scale program source sizeBound code
    bitmap result postSource hypothesis.1 hypothesis.2.1), rest⟩

#print axioms compCorrect_affine
end InitECandidate.Runtime.StackRemove
