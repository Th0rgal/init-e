import InitECandidate.Runtime.EvmInitZeroSuffixBound
import InitECandidate.Runtime.InitializerCounterPrefixes
import InitECandidate.Runtime.ByteStorePrefixReach
import InitECandidate.Runtime.ReachesTerminalBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem source_evmInit_last_address_byte : evmInitAt 41 =
    .seq (.storeByte (.op .add [.var .global (ofString "vm_system_address"),.const 19]) (.const 254))
      (evmInitAt 42) := by
  simp only [evmInitAt,statelessNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem evaluate_evmInit_byte_zero_suffix_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer oldNull oldEmpty : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (nullSlot : state.globals.lookup (ofString "null_address") = some (.val (.word oldNull)))
    (emptySlot : state.globals.lookup (ofString "evm_empty") = some (.val (.word oldEmpty)))
    (aligned : pointer.toNat % 8 = 0) (small : pointer.toNat + 32 ≤ 33806089496)
    (arena : ∀ address : BitVec 64, pointer.toNat ≤ address.toNat →
      address.toNat < pointer.toNat + 32 → state.memaddrs address)
    (budget : 40 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (evmInitAt 41)
    state.clock ≤ evaluated.2.clock + 40 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have prefixRun : Reaches state (evmInitAt 41) (ByteStoreControlFrame state) 0 (evmInitAt 42) := by
    rw [source_evmInit_last_address_byte]
    exact evaluate_storeByte_reaches state _ _ _
  exact evaluate_reaches_terminal_bounded state (evmInitAt 41) (evmInitAt 42)
    (ByteStoreControlFrame state) 0 40 budget prefixRun
    (by
      intro next frame fuel
      exact evaluate_evmInit_zero_suffix_bounded next pointer oldNull oldEmpty
        (frame.2.2.1.trans code) (by rw [frame.1]; exact heap)
        (by rw [frame.1]; exact nullSlot) (by rw [frame.1]; exact emptySlot) aligned small
        (by intro address lower upper; rw [frame.2.2.2]; exact arena address lower upper) fuel)

/-- The actual counter declaration, twenty address stores and complete final
allocation/zeroing suffix consume at most sixty ticks, including failures. -/
theorem evaluate_evmInit_counter_suffix_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer oldNull oldEmpty : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (nullSlot : state.globals.lookup (ofString "null_address") = some (.val (.word oldNull)))
    (emptySlot : state.globals.lookup (ofString "evm_empty") = some (.val (.word oldEmpty)))
    (aligned : pointer.toNat % 8 = 0) (small : pointer.toNat + 32 ≤ 33806089496)
    (arena : ∀ address : BitVec 64, pointer.toNat ≤ address.toNat →
      address.toNat < pointer.toNat + 32 → state.memaddrs address)
    (budget : 60 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (evmInitAt 39)
    state.clock ≤ evaluated.2.clock + 60 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  exact evaluate_reaches_terminal_bounded state (evmInitAt 39) (evmInitAt 41)
    (InitializerCounterFinished state 20) 20 40 budget
    (evaluate_evmInit_counter_prefix state (by omega))
    (by
      intro next frame fuel
      exact evaluate_evmInit_byte_zero_suffix_bounded next pointer oldNull oldEmpty
        (frame.2.1.trans code) (by rw [frame.1]; exact heap)
        (by rw [frame.1]; exact nullSlot) (by rw [frame.1]; exact emptySlot) aligned small
        (by intro address lower upper; rw [frame.2.2.1]; exact arena address lower upper) fuel)

#print axioms source_evmInit_last_address_byte
#print axioms evaluate_evmInit_byte_zero_suffix_bounded
#print axioms evaluate_evmInit_counter_suffix_bounded
end InitECandidate.Runtime
