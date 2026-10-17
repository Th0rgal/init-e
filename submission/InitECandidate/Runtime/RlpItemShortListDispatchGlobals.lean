import InitECandidate.Runtime.RlpItemShortListScopeGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpItem_short_list_after_load_returned_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer total header scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (nonzero : total ≠ 0) (lower : 191 < header.toNat) (upper : header.toNat ≤ 247)
    (inputRange : pointer.toNat + total.toNat < 2^64) (lengthBound : total.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : (header - 192).toNat * ((2 * (header - 192).toNat + 1) * 15 + 19) + 1 ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state rlpItemAfterByte = (some (.returned value),post)) :
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
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
  have guard : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notLower (.const 247) (.var .local (ofString "b"))) = some (.val (.word 1)) := by
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,upper]
  rw [source_rlpItem_single_byte,evaluateHOLFiniteState_seq_line780,first] at run
  dsimp only at run
  rw [source_rlpItem_short_dispatch,evaluateHOLFiniteState_seq_line780,second] at run
  dsimp only at run
  rw [source_rlpItem_long_dispatch,evaluateHOLFiniteState_seq_line780,third] at run
  dsimp only at run
  rw [source_rlpItem_list_dispatch,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard] at run
  simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false] at run
  have terminal := evaluate_rlpItem_short_list_terminal state header headerLocal
  cases selected : evaluateHOLFiniteState state rlpItemShortList with
  | mk result output =>
    rw [selected] at terminal run
    cases result with
    | none => exact False.elim (terminal rfl)
    | some stopped =>
      have same := Prod.mk.inj run
      have globals := rlpItem_short_list_returned_globals state output pointer total header scratch frame ceiling inputLimit
        pointerLocal headerLocal totalLocal nonzero (by omega) upper inputRange lengthBound limitBound
        scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget value (by rw [selected,same.1])
      rw [← same.2]
      exact globals

#print axioms rlpItem_short_list_after_load_returned_globals
end InitECandidate.Runtime
