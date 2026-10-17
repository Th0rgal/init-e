import InitECandidate.Runtime.RlpItemLongListScopeBelow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpItem_long_list_after_load_returned_below {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (pointer total header scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (inputRange : pointer.toNat + total.toNat < 2^64)
    (nonzero : total ≠ 0)
    (lower : 247 < header.toNat) (upper : header.toNat ≤ 255)
    (lengthBound : total.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (ticks : (header - 247).toNat + 2 + (total.toNat * ((2 * total.toNat + 1) * 15 + 19) + 1) ≤ state.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state rlpItemAfterByte = (some (.returned value),final)) (address : BitVec 64) (below : address.toNat < frame.toNat) :
    final.memory address = state.memory address := by
  have first : evaluateHOLFiniteState state
      (.ite (.cmp .lower (.var .local (ofString "b")) (.const 128))
        (.return (.rstruct [.const 0,.var .local (ofString "p"),.const 1,.const 1])) .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    have outside : ¬header.toNat < 128 := by omega
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,outside,evaluateHOLFiniteState_skip]
  have second : evaluateHOLFiniteState state
      (.ite (.cmp .notLower (.const 183) (.var .local (ofString "b"))) rlpItemShortString .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    have outside : ¬header.toNat ≤ 183 := by omega
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,outside,evaluateHOLFiniteState_skip]
  have third : evaluateHOLFiniteState state
      (.ite (.cmp .notLower (.const 191) (.var .local (ofString "b"))) rlpItemLongString .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    have outside : ¬header.toNat ≤ 191 := by omega
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,outside,evaluateHOLFiniteState_skip]
  have fourth : evaluateHOLFiniteState state
      (.ite (.cmp .notLower (.const 247) (.var .local (ofString "b"))) rlpItemShortList .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    have outside : ¬header.toNat ≤ 247 := by omega
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,outside,evaluateHOLFiniteState_skip]
  rw [source_rlpItem_single_byte,evaluateHOLFiniteState_seq_line780,first] at run
  dsimp only at run
  rw [source_rlpItem_short_dispatch,evaluateHOLFiniteState_seq_line780,second] at run
  dsimp only at run
  rw [source_rlpItem_long_dispatch,evaluateHOLFiniteState_seq_line780,third] at run
  dsimp only at run
  rw [source_rlpItem_list_dispatch,evaluateHOLFiniteState_seq_line780,fourth] at run
  exact rlpItem_long_list_returned_below state final pointer total header scratch frame ceiling inputLimit
    pointerLocal headerLocal totalLocal inputRange nonzero lower upper lengthBound limitBound scratchGlobal frameGlobal
    code orderedFrame framePositive scratchBelow arena ticks value run address below

#print axioms rlpItem_long_list_after_load_returned_below
end InitECandidate.Runtime
