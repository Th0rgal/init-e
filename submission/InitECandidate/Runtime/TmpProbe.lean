import InitECandidate.Runtime.OriginalRlpWriterCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

example : sourceFunctionBody Guest.guestFn_rlp_encode_word = .skip := by
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

end InitECandidate.Runtime
