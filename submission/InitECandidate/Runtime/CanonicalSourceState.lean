import InitECandidate.Runtime.CanonicalSourceClock
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE Flapjack

/-- Original source initial state with the globals tail reserved and an
ordinary-memory-compatible backing memory, as required by global lowering. -/
def expandedSourceInitialState (input : Guest.InputBlob) (memory : BitVec 64 → HolWordLab 64) :
    PanSemStateFiniteExact 64 Guest.HostMemory :=
  {sourceInitialState input with
    memory := memory
    memaddrs := fun address => (sourceInitialState input).memaddrs address ∨
      Compiler.Backend.StackRemove.addresses (sourceInitialState input).topAddr globalsWords address
    topAddr := (sourceInitialState input).topAddr + panBytesInWord 64 * BitVec.ofNat 64 globalsWords}

/-- The canonical pre-declaration state is precisely the original source
initializer with the compiler's reserved globals region and backing memory. -/
theorem canonical_pan_declaration_state (input : Guest.InputBlob) :
    canonicalPanDeclarationState input =
      expandedSourceInitialState input (canonicalPanDeclarationState input).memory := by
  have eta : canonicalPanDeclarationState input =
      {sourceInitialState input with
        memory := (canonicalPanDeclarationState input).memory
        memaddrs := (canonicalPanDeclarationState input).memaddrs
        shMemaddrs := (canonicalPanDeclarationState input).shMemaddrs
        clock := (canonicalPanDeclarationState input).clock
        be := (canonicalPanDeclarationState input).be
        ffi := (canonicalPanDeclarationState input).ffi
        baseAddr := (canonicalPanDeclarationState input).baseAddr
        topAddr := (canonicalPanDeclarationState input).topAddr} := by rfl
  rw [canonical_pan_source_domain,canonical_pan_shared_domain,canonical_pan_declaration_clock,
    canonical_pan_endian,canonical_pan_declaration_ffi,canonical_pan_declaration_base,canonical_pan_source_top] at eta
  exact eta

#print axioms canonical_pan_declaration_state
end InitECandidate.Runtime
