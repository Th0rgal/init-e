import InitECandidate.Runtime.EndpointLoopEntry
import InitECandidate.Runtime.BaselineLoopEntry
import InitECandidate.Runtime.BaselineCrepEntryState
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack

/-- Crep entry carrier with the concrete generated code and the exact memory,
heap and FFI fields of the initialized frontend Loop/Word state. -/
noncomputable def endpointCrepState {input : Guest.InputBlob} (entry : EndpointRuntimeEntry input endpoint)
    (base capacity : BitVec 64) : CrepSemHOLState 64 Guest.HostMemory where
  locals := HolFiniteMapExact.empty
  globals := HolFiniteMapExact.empty
  code := HolFiniteMapExact.empty.updateList FrontendStages.pass3.reverse
  memory := wlocWlabHOL ∘ (endpointFrontendState entry).memory
  memaddrs := fun address => (endpointFrontendState entry).mdomain address = true
  shMemaddrs := fun address => (endpointFrontendState entry).shMdomain address = true
  clock := (endpointFrontendState entry).clock
  be := (endpointFrontendState entry).be
  ffi := (endpointFrontendState entry).ffi
  baseAddr := base
  topAddr := base + 2 * capacity

theorem endpointCrepLoop_state {input : Guest.InputBlob} (entry : EndpointRuntimeEntry input endpoint)
    (base capacity : BitVec 64) :
    crepToLoopStateRelExact (endpointCrepState entry base capacity) (endpointLoopState entry base capacity) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem endpointCrepLoop_memory {input : Guest.InputBlob} (entry : EndpointRuntimeEntry input endpoint)
    (base capacity : BitVec 64)
    (words : noLabelsHOL (endpointFrontendState entry).memory
      (fun address => (endpointFrontendState entry).mdomain address = true)) :
    crepToLoopMemRelHOLExact (endpointCrepState entry base capacity).memory
      (endpointLoopState entry base capacity).memory (endpointCrepState entry base capacity).memaddrs := by
  intro address valid
  obtain ⟨word,found⟩ := words address valid
  change wlabWlocExact (wlocWlabHOL ((endpointFrontendState entry).memory address)) = (endpointFrontendState entry).memory address
  rw [found]
  rfl

theorem endpointCrepLoop_globals {input : Guest.InputBlob} (entry : EndpointRuntimeEntry input endpoint)
    (base capacity : BitVec 64) :
    crepToLoopGlobalsRelHOLExact (endpointCrepState entry base capacity).globals
      (endpointLoopState entry base capacity).globals := by
  intro address value found
  change none = some value at found
  cases found

theorem endpointCrepState_bounded {input : Guest.InputBlob} (entry : EndpointRuntimeEntry input endpoint)
    (base capacity : BitVec 64) :
    CrepCodeSize baselineCrepLimit (crepSimpMapcsHOL (endpointCrepState entry base capacity)) :=
  baseline_simplified_crep_bounded _ rfl

#print axioms endpointCrepLoop_state
#print axioms endpointCrepLoop_memory
#print axioms endpointCrepLoop_globals
#print axioms endpointCrepState_bounded
end InitECandidate.Runtime
