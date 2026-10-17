import InitECandidate.Runtime.RlpItemShortListInputDispatchBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Full original short-list execution, including the empty-input check,
actual first-byte load, dispatch and both restored local scopes. -/
theorem evaluate_rlpItem_short_list_input_full_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (byte : UInt8) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (nonzero : length ≠ 0)
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be pointer = some byte)
    (lower : 191 < byte.toNat) (upper : byte.toNat ≤ 247)
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : ((BitVec.ofNat 64 byte.toNat) - 192).toNat * ((2 * ((BitVec.ofNat 64 byte.toNat) - 192).toNat + 1) * 15 + 19) + 1 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item)
    state.clock ≤ evaluated.2.clock + (((BitVec.ofNat 64 byte.toNat) - 192).toNat * ((2 * ((BitVec.ofNat 64 byte.toNat) - 192).toNat + 1) * 15 + 19) + 1) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  let entered := setVarHOLFinite (ofString "b") (.val (.word (BitVec.ofNat 64 byte.toNat))) state
  have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "b" ≠ ofString "p" by decide] using pointerLocal
  have atByte : entered.locals.lookup (ofString "b") = some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atLength : entered.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "b" ≠ ofString "len" by decide] using lengthLocal
  have bound := evaluate_rlpItem_short_list_input_after_load_bounded entered pointer length (BitVec.ofNat 64 byte.toNat) scratch frame ceiling inputLimit
    atPointer atByte (by change 191 < byte.toNat % 2^64; omega)
    (by change byte.toNat % 2^64 ≤ 247; omega)
    atLength nonzero inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
  have check : evaluateHOLFiniteState state
      (.ite (.cmp .equal (.var .local (ofString "len")) (.const 0))
        (.call (some (none,none)) (ofString "rlp_fail") [.const 1]) .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    have notZero : length ≠ BitVec.ofNat 64 0 := nonzero
    simp [evalHOLExact,lengthLocal,Compiler.Encoders.Asm.wordCmpHOL,notZero,evaluateHOLFiniteState_skip]
  rw [source_rlpItem_body,evaluateHOLFiniteState_seq_line780,check]
  dsimp only
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,pointerLocal,loaded,Option.map_some,shapeOfHOLExact,shapeEqHOL,if_true]
  change (let result := evaluateHOLFiniteState entered rlpItemAfterByte; _) ∧ _
  cases run : evaluateHOLFiniteState entered rlpItemAfterByte with
  | mk result post =>
    rw [run] at bound
    exact bound

#print axioms evaluate_rlpItem_short_list_input_full_bounded

theorem rlpItem_short_list_clock_budget (byte : UInt8)
    (lower : 191 < byte.toNat) (upper : byte.toNat ≤ 247) :
    ((BitVec.ofNat 64 byte.toNat) - 192).toNat *
      ((2 * ((BitVec.ofNat 64 byte.toNat) - 192).toNat + 1) * 15 + 19) + 1 ≤ 92621 := by
  have header : (BitVec.ofNat 64 byte.toNat).toNat = byte.toNat := by
    change byte.toNat % 2^64 = byte.toNat
    omega
  have payload : ((BitVec.ofNat 64 byte.toNat) - 192).toNat ≤ 55 := by
    rw [BitVec.toNat_sub_of_le (by apply BitVec.le_def.mpr; change 192 ≤ (BitVec.ofNat 64 byte.toNat).toNat; omega)]
    change (BitVec.ofNat 64 byte.toNat).toNat - 192 ≤ 55
    omega
  have factor : (2 * ((BitVec.ofNat 64 byte.toNat) - 192).toNat + 1) * 15 + 19 ≤ 1684 := by omega
  have product := Nat.mul_le_mul payload factor
  omega

#print axioms rlpItem_short_list_clock_budget
theorem evaluate_rlpItem_short_list_fixed_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (byte : UInt8) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (nonzero : length ≠ 0)
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be pointer = some byte)
    (lower : 191 < byte.toNat) (upper : byte.toNat ≤ 247)
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : 92621 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item)
    state.clock ≤ evaluated.2.clock + (92621) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  have cost := rlpItem_short_list_clock_budget byte lower upper
  have bound := evaluate_rlpItem_short_list_input_full_bounded state pointer length scratch frame byte ceiling inputLimit
    pointerLocal lengthLocal nonzero loaded lower upper inputRange lengthBound limitBound scratchGlobal frameGlobal
    code orderedFrame framePositive scratchBelow arena (by omega)
  dsimp only at bound ⊢
  exact ⟨by omega,bound.2⟩

#print axioms evaluate_rlpItem_short_list_fixed_bounded
end InitECandidate.Runtime
