import InitECandidate.Runtime.KeccakPaddingPrefix
import InitECandidate.Runtime.KeccakAbsorbCallBound
import InitECandidate.Runtime.DiscardCallSuccessLocals
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def keccakOutputScope : ProgHOL 64 :=
  match keccakAfterPadding with
  | .seq _ tail => tail
  | _ => .skip

def keccakPaddingAndAbsorb : ProgHOL 64 :=
  .seq keccakPaddingStores (.call (some (none,none)) (ofString "keccak_absorb_block")
    [.var .local (ofString "stp"),.var .global (ofString "keccak_pad")])

theorem source_keccak_after_padding : keccakAfterPadding =
    .seq (.call (some (none,none)) (ofString "keccak_absorb_block")
      [.var .local (ofString "stp"),.var .global (ofString "keccak_pad")]) keccakOutputScope := by
  simp only [keccakOutputScope,keccakAfterPadding,keccakAfterCopy,keccakAfterPadZero,keccakRemainderTail,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem evaluate_keccak_padding_absorb_group {F : Type} (state : PanSemStateFiniteExact 64 F) :
    evaluateHOLFiniteState state keccakAfterCopy = evaluateHOLFiniteState state (.seq keccakPaddingAndAbsorb keccakOutputScope) := by
  rw [evaluate_keccak_padding_group,source_keccak_after_padding]
  exact (evaluate_seq_assoc state _ _ _).symm

/-- Padding plus absorption is bounded even when padding fails, block loads
fail, or the external permutation terminates. Normal return retains caller locals. -/
theorem evaluate_keccak_padding_absorb_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer pad : BitVec 64)
    (stp : state.locals.lookup (ofString "stp") = some (.val (.word pointer)))
    (padGlobal : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (code : state.code = originalRuntimeCode) (ticks : 19 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state keccakPaddingAndAbsorb = (result,post) ∧
      state.clock ≤ post.clock + 19 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → post.locals = state.locals) ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have padding := evaluate_keccak_padding_control_frame state
  cases paddingRun : evaluateHOLFiniteState state keccakPaddingStores with
  | mk result middle =>
    rw [paddingRun] at padding
    dsimp only at padding
    obtain ⟨control,clock,locals,globals,midCode,domain,endian⟩ := padding
    unfold keccakPaddingAndAbsorb
    rw [evaluateHOLFiniteState_seq_line780,paddingRun]
    rcases control with rfl | rfl
    · have args : evalListHOLFinite middle (h := fun address => Classical.propDecidable (middle.memaddrs address))
          [.var .local (ofString "stp"),.var .global (ofString "keccak_pad")] = some [.val (.word pointer),.val (.word pad)] := by
        simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,locals,globals,stp,padGlobal]
      have contract := evaluate_keccakAbsorb_call_bounded middle _ _ pointer pad (midCode.trans code) args (by omega)
      let call : ProgHOL 64 := .call (some (none,none)) (ofString "keccak_absorb_block")
        [.var .local (ofString "stp"),.var .global (ofString "keccak_pad")]
      cases callRun : evaluateHOLFiniteState middle call with
      | mk result post =>
        change (evaluateHOLFiniteState middle call).2.clock + 19 ≥ middle.clock ∧ _ at contract
        rw [callRun] at contract
        dsimp only at contract
        have metadata := evaluateHOLFiniteState_metadata middle call
        rw [callRun] at metadata
        refine ⟨result,post,callRun,by omega,by omega,contract.2.2,?_,metadata.1.trans midCode,metadata.2.1.trans domain,metadata.2.2.1.trans endian⟩
        intro normal
        have kept := evaluate_discard_call_success_locals middle (ofString "keccak_absorb_block")
          [.var .local (ofString "stp"),.var .global (ofString "keccak_pad")] (by rw [show evaluateHOLFiniteState middle _ = (result,post) from callRun]; exact normal)
        change (evaluateHOLFiniteState middle call).2.locals = middle.locals at kept
        rw [callRun] at kept
        exact kept.trans locals
    · exact ⟨some .error,middle,rfl,by omega,by omega,by simp,(by intro impossible; cases impossible),midCode,domain,endian⟩

#print axioms source_keccak_after_padding
#print axioms evaluate_keccak_padding_absorb_group
#print axioms evaluate_keccak_padding_absorb_bounded
end InitECandidate.Runtime
