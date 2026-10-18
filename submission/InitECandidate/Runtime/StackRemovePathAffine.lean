import InitECandidate.Runtime.StackRemovePathScale
import InitECandidate.Runtime.StackPathAffine
namespace InitECandidate.Runtime.StackRemove
open Flapjack Flapjack.Compiler.Backend.StackLang
open StackToLab

/-- Selected-path stack-removal work is affine in the consumed source clock
for every actual nonerror execution of bounded code with a fixed bitmap table. -/
theorem removePathWork_affine {width : Nat} [NeZero width] {C F : Type}
    (limit scale : Nat) (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (sizeBound : sizeOf p ≤ limit) (code : CodeSizeState limit s) (bitmap : BitmapBudget scale s)
    (result : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F)
    (run : StackSemEvaluate.evaluate (p,s) = (result,post)) (notError : result ≠ some .error) :
    removePathWork p s ≤ scale * ((2 * limit + 2) * (s.clock - post.clock) + 2 * sizeOf p) :=
  Nat.le_trans (removePathWork_scaled scale p s bitmap)
    (Nat.mul_le_mul_left scale (pathWork_affine limit p s sizeBound code result post run notError))

/-- Initial-fuel form of the affine stack-removal work bound. -/
theorem removePathWork_affine_fuel {width : Nat} [NeZero width] {C F : Type}
    (limit scale : Nat) (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (sizeBound : sizeOf p ≤ limit) (code : CodeSizeState limit s) (bitmap : BitmapBudget scale s)
    (result : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F)
    (run : StackSemEvaluate.evaluate (p,s) = (result,post)) (notError : result ≠ some .error) :
    removePathWork p s ≤ scale * ((2 * limit + 2) * s.clock + 2 * limit) :=
  Nat.le_trans (removePathWork_scaled scale p s bitmap)
    (Nat.mul_le_mul_left scale (pathWork_affine_fuel limit p s sizeBound code result post run notError))

#print axioms removePathWork_affine
#print axioms removePathWork_affine_fuel
end InitECandidate.Runtime.StackRemove
