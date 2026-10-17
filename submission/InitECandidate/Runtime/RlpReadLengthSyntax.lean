import InitECandidate.Runtime.ReadOnlyMemory
import InitECandidate.Runtime.ReadOnlyGlobals
import InitECandidate.Proofs.FrontendCodecComputation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpReadLengthAfterCheck : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_rlp_read_length with
  | .seq _ body => body
  | _ => .skip

def rlpReadLengthLoop : ProgHOL 64 :=
  match rlpReadLengthAfterCheck with
  | .dec _ _ _ (.dec _ _ _ (.seq loop _)) => loop
  | _ => .skip

def rlpReadLengthStep : ProgHOL 64 :=
  match rlpReadLengthLoop with
  | .while _ body => body
  | _ => .skip

theorem source_rlpReadLength_step : rlpReadLengthStep =
    .seq (.assign .local (ofString "v") (.op .or
      [.shift .lsl (.var .local (ofString "v")) (.const 8),
       .loadByte (.op .add [.var .local (ofString "p"),.var .local (ofString "i")])]))
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])) := by
  simp only [rlpReadLengthStep,rlpReadLengthLoop,rlpReadLengthAfterCheck,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_rlpReadLength_loop : rlpReadLengthLoop =
    .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) rlpReadLengthStep := by
  simp only [rlpReadLengthStep,rlpReadLengthLoop,rlpReadLengthAfterCheck,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_rlpReadLength_after_check : rlpReadLengthAfterCheck =
    .dec (ofString "v") .one (.const 0) (.dec (ofString "i") .one (.const 0)
      (.seq rlpReadLengthLoop (.return (.var .local (ofString "v"))))) := by
  simp only [rlpReadLengthLoop,rlpReadLengthAfterCheck,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Once the canonical-length check is passed, length decoding only reads
bytes and updates locals, including all exceptional and timeout outcomes. -/
theorem rlpReadLength_after_check_readOnly : readOnlyMemory rlpReadLengthAfterCheck = true := by
  rw [source_rlpReadLength_after_check,source_rlpReadLength_loop,source_rlpReadLength_step]
  rfl

theorem evaluate_rlpReadLength_after_check_frame {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state rlpReadLengthAfterCheck).2.memory = state.memory ∧
    (evaluateHOLFiniteState state rlpReadLengthAfterCheck).2.globals = state.globals := by
  exact ⟨evaluate_readOnly_memory _ rlpReadLength_after_check_readOnly state,
    evaluate_readOnly_globals _ rlpReadLength_after_check_readOnly state⟩

#print axioms source_rlpReadLength_step
#print axioms source_rlpReadLength_loop
#print axioms evaluate_rlpReadLength_after_check_frame
end InitECandidate.Runtime
