import InitECandidate.Runtime.HashGrowZeroHeader
import InitECandidate.Runtime.HashInsertCopyTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The zeroing/header composition is the literal suffix of original growth. -/
theorem source_htabGrow_zero_header :
    sourceFirstCallSuffix (ofString "memzero") (sourceFunctionBody Guest.guestFn_htab_grow) =
      some (hashGrowZeroHeader (.dec (ofString "k") .one (.const 0) (.seq hashGrowRehashLoop (.return (.const 0))))) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_htabGrow_zero_header
end InitECandidate.Runtime
