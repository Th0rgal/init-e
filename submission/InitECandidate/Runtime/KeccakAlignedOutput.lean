import InitECandidate.Runtime.KeccakPaddingAbsorbBound
import InitECandidate.Runtime.StraightLineNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def keccakAlignedOutputStores : ProgHOL 64 :=
  match keccakOutputScope with
  | .seq (.ite _ yes _) _ => yes
  | _ => .skip

def keccakUnalignedOutputCall : ProgHOL 64 :=
  match keccakOutputScope with
  | .seq (.ite _ _ no) _ => no
  | _ => .skip

def keccakAlignedOutput : ProgHOL 64 := .seq keccakAlignedOutputStores (.return (.const 0))

theorem source_keccak_output_scope : keccakOutputScope =
    .seq (.ite (.cmp .equal (.op .and [.var .local (ofString "out"),.const 7]) (.const 0))
      keccakAlignedOutputStores keccakUnalignedOutputCall) (.return (.const 0)) := by
  simp only [keccakAlignedOutputStores,keccakUnalignedOutputCall,keccakOutputScope,keccakAfterPadding,keccakAfterCopy,
    keccakAfterPadZero,keccakRemainderTail,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem keccak_aligned_output_straightLine : straightLine keccakAlignedOutput = true := by
  simp only [keccakAlignedOutput,keccakAlignedOutputStores,keccakOutputScope,keccakAfterPadding,keccakAfterCopy,
    keccakAfterPadZero,keccakRemainderTail,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original aligned output path uses four source word stores and a
return, consuming zero source clock even when an output access fails. -/
theorem evaluate_keccak_aligned_output {F : Type} (state : PanSemStateFiniteExact 64 F) (output : BitVec 64)
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word output)))
    (aligned : output.toNat % 8 = 0) :
    (evaluateHOLFiniteState state keccakOutputScope).2.clock = state.clock ∧
      (evaluateHOLFiniteState state keccakOutputScope).1 ≠ some .timeOut := by
  have mask : output &&& (7 : BitVec 64) = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and]
    change output.toNat &&& (2 ^ 3 - 1) = 0
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact aligned
  have loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .and [.var .local (ofString "out"),.const 7]) = some (.val (.word (0 : BitVec 64))) := by
    simp [evalHOLExact,evalListHOLExact,outLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
    exact mask
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .equal (.op .and [.var .local (ofString "out"),.const 7]) (.const 0)) = some (.val (.word (1 : BitVec 64))) := by
    rw [evalHOLExact,loaded]
    rfl
  have selected : evaluateHOLFiniteState state keccakOutputScope = evaluateHOLFiniteState state keccakAlignedOutput := by
    rw [source_keccak_output_scope,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition]
    unfold keccakAlignedOutput
    rw [evaluateHOLFiniteState_seq_line780]
    rfl
  rw [selected]
  exact ⟨clockPreserving_of_straightLine _ keccak_aligned_output_straightLine state,
    evaluate_straightLine_no_timeout _ keccak_aligned_output_straightLine state⟩

#print axioms source_keccak_output_scope
#print axioms keccak_aligned_output_straightLine
#print axioms evaluate_keccak_aligned_output
end InitECandidate.Runtime
