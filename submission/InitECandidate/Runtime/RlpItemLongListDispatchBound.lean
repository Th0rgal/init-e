import InitECandidate.Runtime.RlpItemLongListScopeBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_rlpItem_long_list_after_load_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer total header scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (lower : 247 < header.toNat)
    (inputRange : pointer.toNat + total.toNat < 2^64)
    (nonzero : total ≠ 0)
    (lengthBound : total.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (ticks : (header - 247).toNat + 2 + (total.toNat * ((2 * total.toNat + 1) * 15 + 19) + 1) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state rlpItemAfterByte
    state.clock ≤ evaluated.2.clock + ((header - 247).toNat + 2 + (total.toNat * ((2 * total.toNat + 1) * 15 + 19) + 1)) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
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
  rw [source_rlpItem_single_byte,evaluateHOLFiniteState_seq_line780,first]
  dsimp only
  rw [source_rlpItem_short_dispatch,evaluateHOLFiniteState_seq_line780,second]
  dsimp only
  rw [source_rlpItem_long_dispatch,evaluateHOLFiniteState_seq_line780,third]
  dsimp only
  rw [source_rlpItem_list_dispatch,evaluateHOLFiniteState_seq_line780,fourth]
  exact evaluate_rlpItem_long_list_bounded state pointer total header scratch frame ceiling inputLimit
    pointerLocal headerLocal totalLocal inputRange nonzero lengthBound limitBound scratchGlobal frameGlobal code
    orderedFrame framePositive scratchBelow arena ticks

#print axioms evaluate_rlpItem_long_list_after_load_bounded
end InitECandidate.Runtime
