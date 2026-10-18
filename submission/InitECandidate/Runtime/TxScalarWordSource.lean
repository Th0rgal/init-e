import InitECandidate.Proofs.FrontendCodecComputation
import InitECandidate.Runtime.SourceClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def txScalarWordAfterField : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_tx_scalar_word with | .decCall _ _ _ _ body => body | _ => .skip
def txScalarWordInitialized : ProgHOL 64 :=
  match txScalarWordAfterField with | .seq _ body => body | _ => .skip
def txScalarWordLoopAndReturn : ProgHOL 64 :=
  match txScalarWordInitialized with | .dec _ _ _ (.dec _ _ _ body) => body | _ => .skip
def txScalarWordLoop : ProgHOL 64 :=
  match txScalarWordLoopAndReturn with | .seq body _ => body | _ => .skip
def txScalarWordStep : ProgHOL 64 :=
  match txScalarWordLoop with | .while _ body => body | _ => .skip

theorem source_txScalarWord_loop : txScalarWordLoop =
    .while (.cmp .lower (.var .local (ofString "j")) (.rfield 1 (.var .local (ofString "f")))) txScalarWordStep := by
  simp only [txScalarWordLoop,txScalarWordLoopAndReturn,txScalarWordInitialized,txScalarWordAfterField,txScalarWordStep,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_txScalarWord_step : txScalarWordStep =
    .seq (.assign .local (ofString "v")
      (.op .or [.shift .lsl (.var .local (ofString "v")) (.const 8),
        .loadByte (.op .add [.rfield 0 (.var .local (ofString "f")),.var .local (ofString "j")])]))
      (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"),.const 1])) := by
  simp only [txScalarWordLoop,txScalarWordLoopAndReturn,txScalarWordInitialized,txScalarWordAfterField,txScalarWordStep,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl
theorem source_txScalarWord_loop_and_return : txScalarWordLoopAndReturn =
    .seq txScalarWordLoop (.return (.var .local (ofString "v"))) := by
  simp only [txScalarWordLoop,txScalarWordLoopAndReturn,txScalarWordInitialized,txScalarWordAfterField,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_txScalarWord_initialized : txScalarWordInitialized =
    .dec (ofString "v") .one (.const 0) (.dec (ofString "j") .one (.const 0) txScalarWordLoopAndReturn) := by
  simp only [txScalarWordLoopAndReturn,txScalarWordInitialized,txScalarWordAfterField,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl
theorem source_txScalarWord_after_field : txScalarWordAfterField =
    .seq (.ite (.cmp .lower (.const 8) (.rfield 1 (.var .local (ofString "f"))))
      (.raise (ofString "TxErr") (.var .local (ofString "envcode"))) .skip) txScalarWordInitialized := by
  simp only [txScalarWordInitialized,txScalarWordAfterField,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl
end InitECandidate.Runtime
