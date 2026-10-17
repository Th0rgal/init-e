import InitECandidate.Runtime.RlpItemLoadedBound
import InitECandidate.Runtime.RlpItemLongFullMemory
import InitECandidate.Runtime.RlpItemShortListFullBelow
import InitECandidate.Runtime.RlpItemLongListFullBelow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpItem_loaded_returned_below {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92632 ≤ state.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item) = (some (.returned value),post)) (address : BitVec 64) (below : address.toNat < frame.toNat) :
    post.memory address = state.memory address := by
  by_cases single : byte.toNat < 128
  · obtain ⟨output,actual,_,memory,_⟩ := evaluate_rlpItem_single_byte_body state pointer length byte
      pointerLocal lengthLocal nonzero single loaded
    have same := (Prod.mk.inj (run.symm.trans actual)).2
    rw [same,memory]
  by_cases short : byte.toNat ≤ 183
  · obtain ⟨result,output,actual,_,_,_,_,_,memory,_⟩ := evaluate_rlpItem_short_full_body state pointer length byte
      pointerLocal lengthLocal nonzero (by omega) short loaded code (by omega)
    have same := (Prod.mk.inj (run.symm.trans actual)).2
    rw [same,memory]
  by_cases longString : byte.toNat ≤ 191
  · have memory := rlpItem_long_full_returned_memory state post pointer length byte value
      pointerLocal lengthLocal nonzero (by omega) longString loaded code (by omega) run
    rw [memory]
  by_cases shortList : byte.toNat ≤ 247
  · have smaller := rlpItem_short_list_clock_budget byte (by omega) shortList
    exact rlpItem_short_list_full_returned_below state post pointer length scratch frame byte ceiling inputLimit
      pointerLocal loaded lengthLocal nonzero (by omega) shortList inputRange lengthBound limitBound scratchGlobal frameGlobal
      code orderedFrame framePositive scratchBelow arena (by omega) value run address below
  · have byteBound := byte.toNat_lt_size
    change byte.toNat < 256 at byteBound
    have headerNat : (BitVec.ofNat 64 byte.toNat).toNat = byte.toNat := by
      change byte.toNat % 2^64 = byte.toNat
      omega
    have smallHeader : ((BitVec.ofNat 64 byte.toNat) - 247).toNat ≤ 8 := by
      rw [BitVec.toNat_sub_of_le (by apply BitVec.le_def.mpr; change 247 ≤ (BitVec.ofNat 64 byte.toNat).toNat; omega)]
      change (BitVec.ofNat 64 byte.toNat).toNat - 247 ≤ 8
      omega
    exact rlpItem_long_list_full_returned_below state post pointer length scratch frame byte ceiling inputLimit
      pointerLocal loaded lengthLocal inputRange nonzero (by omega) (by omega) lengthBound limitBound scratchGlobal frameGlobal
      code orderedFrame framePositive scratchBelow arena (by omega) value run address below

#print axioms rlpItem_loaded_returned_below
end InitECandidate.Runtime
