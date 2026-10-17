import InitECandidate.Runtime.KeccakCopyPrefix
import InitECandidate.Runtime.ByteStoresControlFrame
import InitECandidate.Runtime.PanSeqAssoc
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def keccakPaddingStores : ProgHOL 64 :=
  .seq (.storeByte (.op .add [.var .global (ofString "keccak_pad"),.var .local (ofString "rem")]) (.const 1))
    (.storeByte (.op .add [.var .global (ofString "keccak_pad"),.const 135])
      (.op .or [.loadByte (.op .add [.var .global (ofString "keccak_pad"),.const 135]),.const 128]))

def keccakAfterPadding : ProgHOL 64 :=
  match keccakAfterCopy with
  | .seq _ (.seq _ tail) => tail
  | _ => .skip

theorem source_keccak_padding_prefix : keccakAfterCopy =
    .seq (.storeByte (.op .add [.var .global (ofString "keccak_pad"),.var .local (ofString "rem")]) (.const 1))
      (.seq (.storeByte (.op .add [.var .global (ofString "keccak_pad"),.const 135])
        (.op .or [.loadByte (.op .add [.var .global (ofString "keccak_pad"),.const 135]),.const 128])) keccakAfterPadding) := by
  simp only [keccakAfterPadding,keccakAfterCopy,keccakAfterPadZero,keccakRemainderTail,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem evaluate_keccak_padding_group {F : Type} (state : PanSemStateFiniteExact 64 F) :
    evaluateHOLFiniteState state keccakAfterCopy = evaluateHOLFiniteState state (.seq keccakPaddingStores keccakAfterPadding) := by
  rw [source_keccak_padding_prefix]
  exact (evaluate_seq_assoc state _ _ _).symm

/-- Both original padding stores preserve the call metadata, including early
load/store failure; only successful byte writes can change memory. -/
theorem evaluate_keccak_padding_control_frame {F : Type} (state : PanSemStateFiniteExact 64 F) :
    let output := evaluateHOLFiniteState state keccakPaddingStores;
    (output.1 = none ∨ output.1 = some .error) ∧ output.2.clock = state.clock ∧
      output.2.locals = state.locals ∧ output.2.globals = state.globals ∧ output.2.code = state.code ∧
      output.2.memaddrs = state.memaddrs ∧ output.2.be = state.be := by
  exact evaluate_two_storeBytes_control_frame state _ _ _ _

#print axioms source_keccak_padding_prefix
#print axioms evaluate_keccak_padding_group
#print axioms evaluate_keccak_padding_control_frame
end InitECandidate.Runtime
