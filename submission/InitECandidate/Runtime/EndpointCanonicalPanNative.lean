import InitECandidate.Runtime.EndpointCanonicalCrepNative
import InitECandidate.Runtime.CanonicalCrepNative
import InitECandidate.Runtime.BaselinePanEntryFacts
import InitECandidate.Runtime.PanExceptionDomain
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target

/-- Initialized global-lowered Pancake carrier with the concrete generated
function/exception tables and canonical frontend memory, heap and FFI fields. -/
noncomputable def endpoint_canonicalPanEntryState (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (related : targetStateRel riscvTarget installedAsm endpoint) : PanSemStateFiniteExact 64 Guest.HostMemory where
  locals := HolFiniteMapExact.empty
  globals := HolFiniteMapExact.empty
  structs := []
  code := HolFiniteMapExact.empty.updateList (functionsHOL FrontendStages.pass2).reverse
  eshapes := HolFiniteMapExact.empty.updateList (exceptionsHOL FrontendStages.pass2)
  memory := (endpoint_canonicalCrepState input endpoint related).memory
  memaddrs := (endpoint_canonicalCrepState input endpoint related).memaddrs
  shMemaddrs := (endpoint_canonicalCrepState input endpoint related).shMemaddrs
  clock := (endpoint_canonicalCrepState input endpoint related).clock
  be := (endpoint_canonicalCrepState input endpoint related).be
  ffi := (endpoint_canonicalCrepState input endpoint related).ffi
  baseAddr := (endpoint_canonicalCrepState input endpoint related).baseAddr
  topAddr := (endpoint_canonicalCrepState input endpoint related).topAddr

theorem endpoint_canonical_pan_crep_state (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (related : targetStateRel riscvTarget installedAsm endpoint) (fuel : Nat) :
    panToCrepStateRelFiniteExact {endpoint_canonicalPanEntryState input endpoint related with clock := fuel}
      {endpoint_canonicalCrepState input endpoint related with clock := fuel} :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem endpoint_canonical_crep_code (input : Guest.InputBlob) (endpoint : Flapjack.RiscV.L3.riscv_state)
    (related : targetStateRel riscvTarget installedAsm endpoint) :
    (endpoint_canonicalCrepState input endpoint related).code =
      HolFiniteMapExact.empty.updateList (compileToCrepExactHOLW FrontendStages.pass2).reverse := by
  change HolFiniteMapExact.empty.updateList FrontendStages.pass3.reverse = _
  rw [FrontendStages.toCrep_eq]


#print axioms endpoint_canonical_pan_crep_state
#print axioms endpoint_canonical_crep_code
end InitECandidate.Runtime
