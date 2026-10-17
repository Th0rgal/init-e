import InitECandidate.Runtime.RlpHeaderShortListContract
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpHeaderSingleBranch : ProgHOL 64 :=
  match rlpHeaderAfterByte with | .seq (.ite _ body _) _ => body | _ => .skip

theorem source_rlpHeaderSingle_dispatch : rlpHeaderAfterByte =
    .seq (.ite (.cmp .lower (.var .local (ofString "b")) (.const 128)) rlpHeaderSingleBranch .skip) rlpHeaderAfterSingle := by
  simp only [rlpHeaderSingleBranch,
    rlpHeaderAfterSingle,rlpHeaderAfterByte,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

def rlpHeaderShortStringBranch : ProgHOL 64 :=
  match rlpHeaderAfterSingle with | .seq (.ite _ body _) _ => body | _ => .skip

theorem source_rlpHeaderShortString_dispatch : rlpHeaderAfterSingle =
    .seq (.ite (.cmp .notLower (.const 183) (.var .local (ofString "b"))) rlpHeaderShortStringBranch .skip) rlpHeaderAfterShortString := by
  simp only [rlpHeaderShortStringBranch,rlpHeaderAfterShortString,
    rlpHeaderAfterSingle,rlpHeaderAfterByte,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

def rlpHeaderLongStringBranch : ProgHOL 64 :=
  match rlpHeaderAfterShortString with | .seq (.ite _ body _) _ => body | _ => .skip

theorem source_rlpHeaderLongString_dispatch : rlpHeaderAfterShortString =
    .seq (.ite (.cmp .notLower (.const 191) (.var .local (ofString "b"))) rlpHeaderLongStringBranch .skip) rlpHeaderAfterLongString := by
  simp only [rlpHeaderLongStringBranch,rlpHeaderAfterLongString,rlpHeaderAfterShortString,
    rlpHeaderAfterSingle,rlpHeaderAfterByte,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- On short-list bytes the three preceding header branches leave the state
unchanged; the actual loaded-byte suffix equals the selected short-list branch. -/
theorem evaluate_rlpHeader_short_list_after_load {F : Type} (state : PanSemStateFiniteExact 64 F)
    (header total : BitVec 64)
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (lower : 192 ≤ header.toNat) (upper : header.toNat ≤ 247)
    (nonzero : total ≠ 0) (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock) :
    evaluateHOLFiniteState state rlpHeaderAfterByte = evaluateHOLFiniteState state rlpHeaderShortList := by
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
  rw [source_rlpHeaderSingle_dispatch,evaluateHOLFiniteState_seq_line780,first]
  dsimp only
  rw [source_rlpHeaderShortString_dispatch,evaluateHOLFiniteState_seq_line780,second]
  dsimp only
  rw [source_rlpHeaderLongString_dispatch,evaluateHOLFiniteState_seq_line780,third]
  exact evaluate_rlpHeader_short_list_dispatch state header total headerLocal totalLocal lower upper nonzero code ticks

#print axioms evaluate_rlpHeader_short_list_after_load
end InitECandidate.Runtime
