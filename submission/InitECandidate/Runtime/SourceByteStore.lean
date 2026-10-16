import InitECandidate.Runtime.HashProbeCapacity
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Exact aligned-cell update performed by the source storeByte evaluator. -/
noncomputable def sourceWriteByte {F : Type} (state : PanSemStateFiniteExact 64 F)
    (address value cell : BitVec 64) : PanSemStateFiniteExact 64 F :=
  {state with memory := (fun current =>
    if current = panByteAlignHOL address then
      .word (panSetByteHOL address (BitVec.ofNat 64 (BitVec.ofNat 8 value.toNat).toNat) cell state.be)
    else state.memory current)}

/-- Actual source byte store, including low-byte conversion, aligned-domain
check and complete state update. No clock is consumed. -/
theorem evaluate_source_storeByte {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination expression : ExpHOL 64) (address value cell : BitVec 64)
    (addressEval : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) destination = some (.val (.word address)))
    (valueEval : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) expression = some (.val (.word value)))
    (domain : state.memaddrs (panByteAlignHOL address))
    (memory : state.memory (panByteAlignHOL address) = .word cell) :
    evaluateHOLFiniteState state (.storeByte destination expression) =
      (none,sourceWriteByte state address value cell) := by
  rw [evaluateHOLFiniteState_storeByte,addressEval,valueEval]
  simp [panMemStoreByteWord8HOL,memory,domain,sourceWriteByte]

/-- A byte write cannot alter any other aligned memory word. -/
theorem sourceWriteByte_memory_other {F : Type} (state : PanSemStateFiniteExact 64 F)
    (address value cell current : BitVec 64) (different : current ≠ panByteAlignHOL address) :
    (sourceWriteByte state address value cell).memory current = state.memory current := by
  simp only [sourceWriteByte,if_neg different]

/-- Loads from different aligned words retain success, failure and byte value. -/
theorem sourceWriteByte_load_other_word {F : Type} (state : PanSemStateFiniteExact 64 F)
    (address value cell current : BitVec 64)
    (different : panByteAlignHOL current ≠ panByteAlignHOL address) :
    @panMemLoadByteHOL 64 _ (sourceWriteByte state address value cell).memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be current =
    @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be current := by
  simp [panMemLoadByteHOL,sourceWriteByte,different]

#print axioms evaluate_source_storeByte
#print axioms sourceWriteByte_memory_other
#print axioms sourceWriteByte_load_other_word
end InitECandidate.Runtime
