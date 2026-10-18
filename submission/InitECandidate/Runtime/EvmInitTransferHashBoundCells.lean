import InitECandidate.Runtime.EvmInitTransferHashBound
import InitECandidate.Runtime.AlignedCellDomains
import InitECandidate.Runtime.MemzeroAlignedCallCells
import InitECandidate.Runtime.KeccakShortCallBoundCells
import InitECandidate.Runtime.KeccakInitializerShortCallBoundCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem evaluate_evmInit_transfer_hash_bounded_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (source output : BitVec 64)
    (sourceLocal : state.locals.lookup (ofString "s") = some (.val (.word source)))
    (outputGlobal : state.globals.lookup (ofString "transfer_topic") = some (.val (.word output)))
    (stateGlobal : state.globals.lookup (ofString "keccak_st") = some (.val (.word 2713714976)))
    (padGlobal : state.globals.lookup (ofString "keccak_pad") = some (.val (.word 2713715176)))
    (code : state.code = originalRuntimeCode) (budget : 392 ≤ state.clock)
    (sourceAbove : 2713714688 ≤ source.toNat) (sourceFits : source.toNat + 33 ≤ 33806089496)
    (sourceAligned : source.toNat % 8 = 0) (outputAligned : output.toNat % 8 = 0)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 → 2713714688 ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address) :
    let evaluated := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "keccak256") evmInitTransferHashArguments)
    state.clock ≤ evaluated.2.clock + 392 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut ∧
      evaluated.2.globals = state.globals ∧ evaluated.2.code = state.code ∧ evaluated.2.memaddrs = state.memaddrs ∧
      (evaluated.1 = none → evaluated.2.locals = state.locals) := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      evmInitTransferHashArguments = some [.val (.word source),.val (.word 33),.val (.word output)] := by
    simp [evmInitTransferHashArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,sourceLocal,outputGlobal]
  have bounded := evaluate_keccak_initializer_short_call_bounded_cells state _ _ _ source 33 output
    stateGlobal padGlobal code budget args (by decide) sourceAbove sourceFits sourceAligned outputAligned arena
  refine ⟨bounded.1,bounded.2.1,bounded.2.2.1,bounded.2.2.2.1,bounded.2.2.2.2.1,bounded.2.2.2.2.2,?_⟩
  exact evaluate_discard_call_success_locals state (ofString "keccak256") evmInitTransferHashArguments

#print axioms evaluate_evmInit_transfer_hash_bounded_cells
end InitECandidate.Runtime
