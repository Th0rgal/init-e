import InitECandidate.Runtime.CanonicalMainBuffers
import InitECandidate.Runtime.MainBuffersZeroFields
import InitECandidate.Runtime.MainZeroPrefixCells
import InitECandidate.Runtime.AlignedCellDomains
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def MainDecoderEntry {F : Type} (state ready : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ buffers zero, MainBuffersReady state buffers ∧ ZeroBytePrefix ready zero 32 ∧
    ready.locals = (buffers.locals.update (ofString "si",.val (.word 0))).update
      (ofString "err_code",.val (.word 0)) ∧
    ready.globals = buffers.globals ∧ ready.code = buffers.code ∧ ready.memaddrs = buffers.memaddrs

/-- The authoritative original main reaches its handled decoder call within
the combined initialization, input, allocation and zeroing bound. -/
theorem canonical_main_decoder_entry (input : Guest.InputBlob) (fuel : Nat)
    (budget : ((1893 + (inputBlobBodyCost + 1)) + 4) + 33 ≤ fuel) :
    let state := {canonicalOriginalSourceEntry input with clock := fuel}
    Reaches state (mainAt 0) (MainDecoderEntry state)
      (((1893 + (inputBlobBodyCost + 1)) + 4) + 33) (mainAt 20) := by
  let state := {canonicalOriginalSourceEntry input with clock := fuel}
  change Reaches state (mainAt 0) (MainDecoderEntry state)
    (((1893 + (inputBlobBodyCost + 1)) + 4) + 33) (mainAt 20)
  have clock : state.clock = fuel := rfl
  have reached := canonical_main_buffers input fuel (by omega)
  change Reaches state (mainAt 0) (MainBuffersReady state)
    ((1893 + (inputBlobBodyCost + 1)) + 4) (mainAt 17) at reached
  rcases reached with ⟨buffers,valid,spent,remaining,agreement⟩ | aborted
  · obtain ⟨zero,binding,aligned,lower,upper,installed,domain⟩ := valid.zero_fields
    have domains := aligned_interval_byte_domains buffers zero 32 aligned
      (by change zero.toNat + 32 ≤ 2 ^ 64; omega)
      (by
        intro address cellAligned lo hi
        rw [domain]
        exact canonical_original_aligned_arena input address cellAligned (by omega)
          (by change address.toNat < zero.toNat + 32 at hi; omega))
    obtain ⟨ready,tailAgreement,tailSpent,tailRemaining,zeroed,locals,globals,code,addresses⟩ :=
      evaluate_main_zero_prefix_cells buffers zero binding
        (installed.trans (canonical_original_source_code input)) (by omega) upper aligned domains
    left
    exact ⟨ready,⟨buffers,zero,valid,zeroed,locals,globals,code,addresses⟩,
      by omega,by omega,scoped_trans agreement tailAgreement⟩
  · right
    exact stAbort_mono state _ ((1893 + (inputBlobBodyCost + 1)) + 4)
      (((1893 + (inputBlobBodyCost + 1)) + 4) + 33) (by omega) aborted

#print axioms canonical_main_decoder_entry
end InitECandidate.Runtime
