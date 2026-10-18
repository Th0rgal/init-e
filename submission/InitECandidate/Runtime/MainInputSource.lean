import InitECandidate.Runtime.MainSszHandlerSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem source_main_input_declaration : mainAt 14 =
    .decCall (ofString "inp") (.comb [.one,.one]) (ofString "input_blob") [] (mainAt 15) := by
  simp only [mainAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_main_output_declaration : mainAt 15 =
    .decCall (ofString "out") .one (ofString "alloc") [.const 256] (mainAt 16) := by
  simp only [mainAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_main_zero_declaration : mainAt 16 =
    .decCall (ofString "z32") .one (ofString "alloc") [.const 32] (mainAt 17) := by
  simp only [mainAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_main_zero_call : mainAt 17 =
    .seq (.call (some (none,none)) (ofString "memzero")
      [.var .local (ofString "z32"),.const 32]) (mainAt 18) := by
  simp only [mainAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_main_si_declaration : mainAt 18 =
    .dec (ofString "si") .one (.const 0) (mainAt 19) := by
  simp only [mainAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_main_error_declaration : mainAt 19 =
    .dec (ofString "err_code") .one (.const 0) (mainAt 20) := by
  simp only [mainAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_main_input_declaration
#print axioms source_main_output_declaration
#print axioms source_main_zero_declaration
#print axioms source_main_zero_call
#print axioms source_main_si_declaration
#print axioms source_main_error_declaration
end InitECandidate.Runtime
