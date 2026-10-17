import InitECandidate.Runtime.RlpHeaderShortListDispatch
import InitECandidate.Runtime.RlpHeaderLongListContract
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- On long-list bytes the four preceding header branches leave the state
unchanged; the actual loaded-byte suffix equals the selected long-list branch. -/
theorem evaluate_rlpHeader_long_list_after_load {F : Type} (state : PanSemStateFiniteExact 64 F)
    (header : BitVec 64)
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (lower : 247 < header.toNat) :
    evaluateHOLFiniteState state rlpHeaderAfterByte = evaluateHOLFiniteState state rlpHeaderLongList := by
  have single : ¬header.toNat < 128 := by omega
  have short : ¬header.toNat ≤ 183 := by omega
  have long : ¬header.toNat ≤ 191 := by omega
  have first : evaluateHOLFiniteState state
      (.ite (.cmp .lower (.var .local (ofString "b")) (.const 128)) rlpHeaderSingleBranch .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,single,evaluateHOLFiniteState_skip]
  have second : evaluateHOLFiniteState state
      (.ite (.cmp .notLower (.const 183) (.var .local (ofString "b"))) rlpHeaderShortStringBranch .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,short,evaluateHOLFiniteState_skip]
  have third : evaluateHOLFiniteState state
      (.ite (.cmp .notLower (.const 191) (.var .local (ofString "b"))) rlpHeaderLongStringBranch .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,long,evaluateHOLFiniteState_skip]
  have list : ¬header.toNat ≤ 247 := by omega
  have fourth : evaluateHOLFiniteState state
      (.ite (.cmp .notLower (.const 247) (.var .local (ofString "b"))) rlpHeaderShortList .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    simp [evalHOLExact,headerLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,list,evaluateHOLFiniteState_skip]
  rw [source_rlpHeaderSingle_dispatch,evaluateHOLFiniteState_seq_line780,first]
  dsimp only
  rw [source_rlpHeaderShortString_dispatch,evaluateHOLFiniteState_seq_line780,second]
  dsimp only
  rw [source_rlpHeaderLongString_dispatch,evaluateHOLFiniteState_seq_line780,third]
  dsimp only
  rw [source_rlpHeader_short_list_dispatch,evaluateHOLFiniteState_seq_line780,fourth]
  rfl

#print axioms evaluate_rlpHeader_long_list_after_load
end InitECandidate.Runtime
