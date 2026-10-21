import InitECandidate.Runtime.StackNativeGapPrice
import InitECandidate.Runtime.LabInstructionPaddingBounds
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm

/-- Encoding and following padding share one span. Control nodes retain the
original full-span prices because their expansion is accounted differently. -/
noncomputable def refinedNativeLocalPrice {F : Type} : ExecutionLocalPrice F := fun p source code =>
  match p with
  | .inst (.const rd value) => max (instLocalCost (.const rd value)) (encodedLineWords code)
  | .inst instruction => instLocalCost instruction + (encodedLineWords code - 1)
  | .tick => instLocalCost .skip + (encodedLineWords code - 1)
  | _ => nativeLocalPrice p source code

/-- Refined local prices satisfy the actual encoder/flattening obligations,
with no instruction-fetch or desired whole-runtime bound supplied. -/
theorem refinedNativeLocalPrice_caps {F : Type} : LocalNativeCaps (refinedNativeLocalPrice (F := F)) := by
  refine {
    instruction := ?_
    location := nativeLocalPrice_caps.location
    tick := ?_
    breakPrice := nativeLocalPrice_caps.breakPrice
    returnPrice := nativeLocalPrice_caps.returnPrice
    raisePrice := nativeLocalPrice_caps.raisePrice
    ffi := nativeLocalPrice_caps.ffi
    shared := nativeLocalPrice_caps.shared
    branch := nativeLocalPrice_caps.branch
    loopPrice := nativeLocalPrice_caps.loopPrice
    tailCall := nativeLocalPrice_caps.tailCall
    rawCall := nativeLocalPrice_caps.rawCall
    returnCall := nativeLocalPrice_caps.returnCall
    jumpLower := nativeLocalPrice_caps.jumpLower }
  · intro source instruction encoded pc
    cases instruction with
    | const rd value => exact constantInstructionWork_max encoded pc (encodedLineWords encoded) rd value (encodedLineWords_bound encoded pc)
    | skip => exact instructionWork_padding_bound encoded pc (encodedLineWords encoded) .skip (encodedLineWords_bound encoded pc)
    | arith op => exact instructionWork_padding_bound encoded pc (encodedLineWords encoded) (.arith op) (encodedLineWords_bound encoded pc)
    | mem op reg addr => exact instructionWork_padding_bound encoded pc (encodedLineWords encoded) (.mem op reg addr) (encodedLineWords_bound encoded pc)
  · intro source encoded pc
    exact instructionWork_padding_bound encoded pc (encodedLineWords encoded) .skip (encodedLineWords_bound encoded pc)

noncomputable def refinedNativePriceWithGap (gap : Nat) : HolProg 64 → Nat
  | .inst (.const rd value) => max (instLocalCost (.const rd value)) gap
  | .inst instruction => instLocalCost instruction + (gap-1)
  | .tick => instLocalCost .skip + (gap-1)
  | p => nativePriceWithGap gap p

theorem refinedNativeLocalPrice_le {F : Type} (gap : Nat) (encoded : LabProgHOL 64)
    (bounded : encodedLineWords encoded ≤ gap) (p : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    refinedNativeLocalPrice p source encoded ≤ refinedNativePriceWithGap gap p := by
  cases p <;> try (dsimp only [refinedNativeLocalPrice, refinedNativePriceWithGap]; exact nativeLocalPrice_le gap encoded bounded _ source)
  case inst instruction =>
    cases instruction <;> simp only [refinedNativeLocalPrice, refinedNativePriceWithGap]
    · exact Nat.add_le_add_left (Nat.sub_le_sub_right bounded 1) _
    · exact max_le_max (Nat.le_refl _) bounded
    · exact Nat.add_le_add_left (Nat.sub_le_sub_right bounded 1) _
    · exact Nat.add_le_add_left (Nat.sub_le_sub_right bounded 1) _
  case tick =>
    exact Nat.add_le_add_left (Nat.sub_le_sub_right bounded 1) _

#print axioms refinedNativeLocalPrice_caps
#print axioms refinedNativeLocalPrice_le
end InitECandidate.Runtime.StackToLab
