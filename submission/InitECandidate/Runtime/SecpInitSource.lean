import InitECandidate.Runtime.OriginalSecpInitCode
import InitECandidate.Runtime.StoreFourWords
import InitECandidate.Runtime.DecodeRequestsStoresReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_secpAccelInitBlock_body : sourceFunctionBody Guest.guestFn_secp_accel_init_block =
    .seq (.store (.op .add [.var .local (ofString "base"),.const 64]) (.rstruct [.const 0,.const 0,.const 0,.const 0]))
      (.seq (.store (.op .add [.var .local (ofString "base"),.const 96]) (.var .local (ofString "modulus")))
        (.return (.const 0))) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_secpAccelInitBlock_body

theorem source_secp256k1Init_body : sourceFunctionBody Guest.guestFn_secp256k1_init =
    .seq (.ite (.cmp .notEqual (.var .global (ofString "secp_accel_scratch")) (.const 0))
      (.return (.const 0)) .skip)
    (.seq (.call (some (some (.global,ofString "secp_accel_scratch"),none)) (ofString "alloc")
        [.op .add [.panop .mul [.const 2,.const 160],.const 128]])
      (.seq (.call (some (none,none)) (ofString "secp_accel_init_block")
          [.op .add [.var .global (ofString "secp_accel_scratch"),.const 0],
           .rstruct [.const 18446744069414583343,.const 18446744073709551615,.const 18446744073709551615,.const 18446744073709551615]])
        (.seq (.call (some (none,none)) (ofString "secp_accel_init_block")
            [.op .add [.var .global (ofString "secp_accel_scratch"),.const 160],
             .rstruct [.const 13822214165235122497,.const 13451932020343611451,.const 18446744073709551614,.const 18446744073709551615]])
          (.return (.const 0))))) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_secp256k1Init_body
end InitECandidate.Runtime
