import InitECandidate.Runtime.EndpointCrepNativeAffine
import InitECandidate.Runtime.BaselineCrepNative
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target

noncomputable def endpoint_canonicalRuntimeEntry (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (related : targetStateRel riscvTarget installedAsm endpoint) : EndpointRuntimeEntry input endpoint :=
  Classical.choose (endpointRuntimeEntry_exists input endpoint related)

theorem endpoint_canonical_source_registers (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (related : targetStateRel riscvTarget installedAsm endpoint) :
    (endpoint_canonicalRuntimeEntry input endpoint related).asm.regs 11 = BitVec.ofNat 64 sourceBase ∧
    (endpoint_canonicalRuntimeEntry input endpoint related).asm.regs 12 = BitVec.ofNat 64 stackStart ∧
    (endpoint_canonicalRuntimeEntry input endpoint related).asm.regs 13 = BitVec.ofNat 64 ramEnd :=
  (Classical.choose_spec (endpointRuntimeEntry_exists input endpoint related)).2

noncomputable def endpoint_canonicalHeapBase (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (related : targetStateRel riscvTarget installedAsm endpoint) : BitVec 64 :=
  Classical.choose (endpointLoopState_exists (endpoint_canonicalRuntimeEntry input endpoint related))

noncomputable def endpoint_canonicalHeapCapacity (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (related : targetStateRel riscvTarget installedAsm endpoint) : BitVec 64 :=
  Classical.choose (Classical.choose_spec (endpointLoopState_exists (endpoint_canonicalRuntimeEntry input endpoint related)))

theorem endpoint_canonical_frontend_noLabels (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (related : targetStateRel riscvTarget installedAsm endpoint) :
    noLabelsHOL (endpointFrontendState (endpoint_canonicalRuntimeEntry input endpoint related)).memory
      (fun address => (endpointFrontendState (endpoint_canonicalRuntimeEntry input endpoint related)).mdomain address = true) :=
  by
  intro address valid
  change (endpoint_canonicalRuntimeEntry input endpoint related).source.mdomain address = true at valid
  change ∃ word, (endpoint_canonicalRuntimeEntry input endpoint related).source.memory address = WordLocW.word word
  exact (Classical.choose_spec (endpointRuntimeEntry_exists input endpoint related)).1 address valid

theorem endpoint_canonical_loop_related (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (related : targetStateRel riscvTarget installedAsm endpoint) :
    loopToWordStateRelHOLExact
      (endpointLoopState (endpoint_canonicalRuntimeEntry input endpoint related) (endpoint_canonicalHeapBase input endpoint related) (endpoint_canonicalHeapCapacity input endpoint related))
      (endpointFrontendState (endpoint_canonicalRuntimeEntry input endpoint related)) :=
  Classical.choose_spec (Classical.choose_spec (endpointLoopState_exists (endpoint_canonicalRuntimeEntry input endpoint related)))

noncomputable def endpoint_canonicalCrepState (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (related : targetStateRel riscvTarget installedAsm endpoint) : CrepSemHOLState 64 Guest.HostMemory :=
  endpointCrepState (endpoint_canonicalRuntimeEntry input endpoint related) (endpoint_canonicalHeapBase input endpoint related) (endpoint_canonicalHeapCapacity input endpoint related)


#print axioms endpoint_canonical_source_registers
#print axioms endpoint_canonical_frontend_noLabels
#print axioms endpoint_canonical_loop_related
end InitECandidate.Runtime
