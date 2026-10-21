import InitECandidate.Proofs.BackendStages.Native
import InitECandidate.Runtime.StackRemovalLocalCost
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace InitECandidate.Runtime.FineCost
open Flapjack InitECandidate.Proofs
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackRemove

/-- Kernel-checked fact about the actual submitted compiler output, not a
multiplier applied to every operation. Used to discharge immediate addressing. -/
theorem guest_frame_sizes_checked :
    BackendStages.Native.frames0.all (fun frame => decide (frame ≤ 92)) = true := by
  decide_cbv

theorem guest_frame_size_bound (frame : Nat)
    (present : frame ∈ BackendStages.Native.frames0) : frame ≤ 92 := by
  have checked := guest_frame_sizes_checked
  simp only [List.all_eq_true, decide_eq_true_eq] at checked
  exact checked frame present

/-- Exact target addressing check for every possible slot in these frames. -/
theorem small_frame_offsets_checked :
    (List.range 93).all (fun slot =>
      asmOffsetOkExact 0 riscvConfig.addrOffset (wordOffset slot)) = true := by
  decide_cbv

theorem small_frame_slot_direct (slot : Nat) (small : slot ≤ 92) :
    asmOffsetOkExact 0 riscvConfig.addrOffset (wordOffset slot) = true := by
  have checked := small_frame_offsets_checked
  simp only [List.all_eq_true] at checked
  exact checked slot (List.mem_range.mpr (by omega))

/-- Actual frame membership discharges direct-address applicability; 92 is
not a cost multiplier. Truncated frame-slot arithmetic stays below the frame. -/
theorem guest_spill_slot_direct (frame slot : Nat)
    (present : frame ∈ BackendStages.Native.frames0) (within : slot ≤ frame) :
    asmOffsetOkExact 0 riscvConfig.addrOffset (wordOffset slot) = true :=
  small_frame_slot_direct slot (Nat.le_trans within (guest_frame_size_bound frame present))

theorem guest_spill_load_units (frame slot register : Nat)
    (present : frame ∈ BackendStages.Native.frames0) (within : slot ≤ frame) :
    stackRemovalUnits riscvConfig.addrOffset
      (.stackLoad register slot : Compiler.Backend.StackLang.HolProg 64) = 1 := by
  simp only [stackRemovalUnits, guest_spill_slot_direct frame slot present within, ↓reduceIte]

theorem guest_spill_store_units (frame slot register : Nat)
    (present : frame ∈ BackendStages.Native.frames0) (within : slot ≤ frame) :
    stackRemovalUnits riscvConfig.addrOffset
      (.stackStore register slot : Compiler.Backend.StackLang.HolProg 64) = 1 := by
  simp only [stackRemovalUnits, guest_spill_slot_direct frame slot present within, ↓reduceIte]

#print axioms guest_frame_size_bound
#print axioms guest_spill_load_units
#print axioms guest_spill_store_units
end InitECandidate.Runtime.FineCost
