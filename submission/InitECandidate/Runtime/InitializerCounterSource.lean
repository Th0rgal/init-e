import InitECandidate.Runtime.InitializerByteCounterLoop
import InitECandidate.Runtime.StatelessInputSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def evmInitAt : Nat → ProgHOL 64
  | 0 => sourceFunctionBody Guest.guestFn_evm_init
  | n + 1 => statelessNext (evmInitAt n)
def forkInitAt : Nat → ProgHOL 64
  | 0 => sourceFunctionBody Guest.guestFn_fork_init
  | n + 1 => statelessNext (forkInitAt n)

def evmInitCounterDestination : ExpHOL 64 :=
  .op .add [.var .global (ofString "vm_system_address"),.var .local (ofString "i")]
def forkInitCounterDestination : ExpHOL 64 :=
  .op .add [.var .global (ofString "precompile_addrs"),
    .panop .mul [.var .local (ofString "i"),.const 20],.const 19]
def forkInitCounterValue : ExpHOL 64 :=
  .op .add [.var .local (ofString "i"),.const 1]

theorem source_evmInit_counter_declaration : evmInitAt 39 =
    .dec (ofString "i") .one (.const 0) (evmInitAt 40) := by
  simp only [evmInitAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_evmInit_counter_loop : evmInitAt 40 =
    .seq (initializerByteCounterLoop 20 evmInitCounterDestination (.const 255)) (evmInitAt 41) := by
  simp only [evmInitAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_forkInit_counter_declaration : forkInitAt 4 =
    .dec (ofString "i") .one (.const 0) (forkInitAt 5) := by
  simp only [forkInitAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_forkInit_counter_loop : forkInitAt 5 =
    .seq (initializerByteCounterLoop 17 forkInitCounterDestination forkInitCounterValue) (forkInitAt 6) := by
  simp only [forkInitAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_evmInit_counter_declaration
#print axioms source_evmInit_counter_loop
#print axioms source_forkInit_counter_declaration
#print axioms source_forkInit_counter_loop
end InitECandidate.Runtime
