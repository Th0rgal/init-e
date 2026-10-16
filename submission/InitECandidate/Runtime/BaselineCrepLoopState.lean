import InitECandidate.Runtime.BaselineLoopEntry
import InitECandidate.Runtime.BaselineCrepEntryState
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack

/-- Crep entry carrier with the concrete generated code and the exact memory,
heap and FFI fields of the initialized frontend Loop/Word state. -/
noncomputable def entryCrepState {input : Guest.InputBlob} (entry : BaselineRuntimeEntry input)
    (base capacity : BitVec 64) : CrepSemHOLState 64 Guest.HostMemory where
  locals := HolFiniteMapExact.empty
  globals := HolFiniteMapExact.empty
  code := HolFiniteMapExact.empty.updateList FrontendStages.pass3.reverse
  memory := wlocWlabHOL ∘ (entryFrontendState entry).memory
  memaddrs := fun address => (entryFrontendState entry).mdomain address = true
  shMemaddrs := fun address => (entryFrontendState entry).shMdomain address = true
  clock := (entryFrontendState entry).clock
  be := (entryFrontendState entry).be
  ffi := (entryFrontendState entry).ffi
  baseAddr := base
  topAddr := base + 2 * capacity

theorem entryCrepLoop_state {input : Guest.InputBlob} (entry : BaselineRuntimeEntry input)
    (base capacity : BitVec 64) :
    crepToLoopStateRelExact (entryCrepState entry base capacity) (entryLoopState entry base capacity) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem entryCrepLoop_memory {input : Guest.InputBlob} (entry : BaselineRuntimeEntry input)
    (base capacity : BitVec 64)
    (words : noLabelsHOL (entryFrontendState entry).memory
      (fun address => (entryFrontendState entry).mdomain address = true)) :
    crepToLoopMemRelHOLExact (entryCrepState entry base capacity).memory
      (entryLoopState entry base capacity).memory (entryCrepState entry base capacity).memaddrs := by
  intro address valid
  obtain ⟨word,found⟩ := words address valid
  change wlabWlocExact (wlocWlabHOL ((entryFrontendState entry).memory address)) = (entryFrontendState entry).memory address
  rw [found]
  rfl

theorem entryCrepLoop_globals {input : Guest.InputBlob} (entry : BaselineRuntimeEntry input)
    (base capacity : BitVec 64) :
    crepToLoopGlobalsRelHOLExact (entryCrepState entry base capacity).globals
      (entryLoopState entry base capacity).globals := by
  intro address value found
  change none = some value at found
  cases found

theorem entryCrepState_bounded {input : Guest.InputBlob} (entry : BaselineRuntimeEntry input)
    (base capacity : BitVec 64) :
    CrepCodeSize baselineCrepLimit (crepSimpMapcsHOL (entryCrepState entry base capacity)) :=
  baseline_simplified_crep_bounded _ rfl

#print axioms entryCrepLoop_state
#print axioms entryCrepLoop_memory
#print axioms entryCrepLoop_globals
#print axioms entryCrepState_bounded
end InitECandidate.Runtime
