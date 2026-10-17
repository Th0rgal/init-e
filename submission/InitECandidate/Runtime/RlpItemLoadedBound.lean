import InitECandidate.Runtime.RlpItemShortListInputFullBound
import InitECandidate.Runtime.RlpItemLongListFullBound
import InitECandidate.Runtime.RlpItemShortFullBody
import InitECandidate.Runtime.RlpItemLongFullBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- All five RLP header classes share this input-quadratic source-clock
budget, including every nested validation and rejection outcome. -/
theorem evaluate_rlpItem_loaded_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (byte : UInt8) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (nonzero : length ≠ 0)
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be pointer = some byte)
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92632 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item)
    state.clock ≤ evaluated.2.clock + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92632) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  by_cases single : byte.toNat < 128
  · obtain ⟨post,run,clock,_⟩ := evaluate_rlpItem_single_byte_body state pointer length byte
      pointerLocal lengthLocal nonzero single loaded
    dsimp only
    rw [run]
    dsimp only
    exact ⟨by omega,by omega,by simp⟩
  by_cases short : byte.toNat ≤ 183
  · obtain ⟨result,post,run,cost,remaining,noTimeout,_⟩ := evaluate_rlpItem_short_full_body state pointer length byte
      pointerLocal lengthLocal nonzero (by omega) short loaded code (by omega)
    dsimp only
    rw [run]
    dsimp only
    exact ⟨by omega,remaining,noTimeout⟩
  by_cases longString : byte.toNat ≤ 191
  · obtain ⟨result,post,run,cost,remaining,noTimeout,_⟩ := evaluate_rlpItem_long_full_body_bounded state pointer length byte
      pointerLocal lengthLocal nonzero (by omega) longString loaded code (by omega)
    dsimp only
    rw [run]
    dsimp only
    exact ⟨by omega,remaining,noTimeout⟩
  by_cases shortList : byte.toNat ≤ 247
  · have bound := evaluate_rlpItem_short_list_fixed_bounded state pointer length scratch frame byte ceiling inputLimit
      pointerLocal lengthLocal nonzero loaded (by omega) shortList inputRange lengthBound limitBound
      scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena (by omega)
    dsimp only at bound ⊢
    exact ⟨by omega,bound.2⟩
  · have byteBound := byte.toNat_lt_size
    change byte.toNat < 256 at byteBound
    have headerNat : (BitVec.ofNat 64 byte.toNat).toNat = byte.toNat := by
      change byte.toNat % 2^64 = byte.toNat
      omega
    have smallHeader : ((BitVec.ofNat 64 byte.toNat) - 247).toNat ≤ 8 := by
      rw [BitVec.toNat_sub_of_le (by apply BitVec.le_def.mpr; change 247 ≤ (BitVec.ofNat 64 byte.toNat).toNat; omega)]
      change (BitVec.ofNat 64 byte.toNat).toNat - 247 ≤ 8
      omega
    have bound := evaluate_rlpItem_long_list_full_bounded state pointer length scratch frame byte ceiling inputLimit
      pointerLocal lengthLocal nonzero loaded (by omega) inputRange lengthBound limitBound
      scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena (by omega)
    dsimp only at bound ⊢
    exact ⟨by omega,bound.2⟩

#print axioms evaluate_rlpItem_loaded_bounded
end InitECandidate.Runtime
