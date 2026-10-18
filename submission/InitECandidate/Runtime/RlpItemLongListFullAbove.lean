import InitECandidate.Runtime.RlpItemLongListDispatchAbove
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpItem_long_list_full_returned_above {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer total scratch frame : BitVec 64) (byte : UInt8) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be pointer = some byte)
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (inputRange : pointer.toNat + total.toNat < 2^64)
    (nonzero : total ≠ 0)
    (lower : 247 < byte.toNat) (upper : byte.toNat ≤ 255)
    (lengthBound : total.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (ticks : ((BitVec.ofNat 64 byte.toNat) - 247).toNat + 2 + (total.toNat * ((2 * total.toNat + 1) * 15 + 19) + 1) ≤ state.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item) = (some (.returned value),post)) (address : BitVec 64) (above : ceiling ≤ address.toNat) :
    post.memory address = state.memory address := by
  have check : evaluateHOLFiniteState state
      (.ite (.cmp .equal (.var .local (ofString "len")) (.const 0))
        (.call (some (none,none)) (ofString "rlp_fail") [.const 1]) .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    have notZero : total ≠ BitVec.ofNat 64 0 := nonzero
    simp [evalHOLExact,totalLocal,Compiler.Encoders.Asm.wordCmpHOL,notZero,evaluateHOLFiniteState_skip]
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.loadByte (.var .local (ofString "p"))) = some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
    simp [evalHOLExact,pointerLocal,loaded]
  rw [source_rlpItem_body,evaluateHOLFiniteState_seq_line780,check] at run
  obtain ⟨output,bodyRun,restored⟩ := evaluate_dec_word_result_scope state post (ofString "b")
    (.loadByte (.var .local (ofString "p"))) (BitVec.ofNat 64 byte.toNat) rlpItemAfterByte
    (some (.returned value)) initializer run
  let entered := setVarHOLFinite (ofString "b") (.val (.word (BitVec.ofNat 64 byte.toNat))) state
  have localFrame : ∀ name, name ≠ ofString "b" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have atByte : entered.locals.lookup (ofString "b") = some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atTotal : entered.locals.lookup (ofString "len") = some (.val (.word total)) := by
    rw [localFrame _ (by decide)]
    exact totalLocal
  have globals := rlpItem_long_list_after_load_returned_above entered output pointer total (BitVec.ofNat 64 byte.toNat) scratch frame ceiling inputLimit
    ((localFrame _ (by decide)).trans pointerLocal) atByte atTotal inputRange nonzero
    (by change 247 < byte.toNat % 2^64; omega) (by change byte.toNat % 2^64 ≤ 255; omega)
    lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena ticks value bodyRun address above
  rw [restored]
  exact globals

#print axioms rlpItem_long_list_full_returned_above
end InitECandidate.Runtime
