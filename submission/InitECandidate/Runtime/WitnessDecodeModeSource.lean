import InitECandidate.Runtime.DecodeWitnessNodeLoopSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def witnessDecodeTail : ProgHOL 64 :=
  match decodeWitnessNodeDecodeMode with | .decCall _ _ _ _ tail => tail | _ => .skip

def witnessDecodeCompleted : ProgHOL 64 :=
  match witnessDecodeTail with | .ite _ completed _ => completed | _ => .skip

def witnessDecodePush : ProgHOL 64 :=
  match witnessDecodeTail with | .ite _ _ pending => pending | _ => .skip

theorem source_witness_decode_call : decodeWitnessNodeDecodeMode =
  .decCall (ofString "d") (.comb [.one,.one]) (ofString "_decode_step")
    [.var .local (ofString "db"),.var .local (ofString "cur_p"),.var .local (ofString "cur_n")] witnessDecodeTail := by
  simp only [witnessDecodeTail,decodeWitnessNodeDecodeMode,decodeWitnessNodeIteration,
    decodeWitnessNodeBodyAt,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_witness_decode_tail : witnessDecodeTail =
  .ite (.cmp .equal (.rfield 0 (.var .local (ofString "d"))) (.const 0)) witnessDecodeCompleted witnessDecodePush := by
  simp only [witnessDecodeTail,witnessDecodeCompleted,witnessDecodePush,decodeWitnessNodeDecodeMode,
    decodeWitnessNodeIteration,decodeWitnessNodeBodyAt,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_witness_decode_completed : witnessDecodeCompleted =
  .seq (.assign .local (ofString "result") (.rfield 1 (.var .local (ofString "d"))))
    (.assign .local (ofString "mode") (.const 0)) := by
  simp only [witnessDecodeCompleted,witnessDecodeTail,decodeWitnessNodeDecodeMode,decodeWitnessNodeIteration,
    decodeWitnessNodeBodyAt,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_witness_decode_push : witnessDecodePush =
  .seq (.store (.op .add [.rfield 1 (.var .local (ofString "d")),.const 0]) (.var .local (ofString "top")))
  (.seq (.assign .local (ofString "top") (.rfield 1 (.var .local (ofString "d"))))
  (.seq (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "top"),.const 8])) (.const 1))
    (.assign .local (ofString "slot") (.const 1)) (.assign .local (ofString "slot") (.const 0)))
    (.assign .local (ofString "mode") (.const 2)))) := by
  simp only [witnessDecodePush,witnessDecodeTail,decodeWitnessNodeDecodeMode,decodeWitnessNodeIteration,
    decodeWitnessNodeBodyAt,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_witness_decode_call
#print axioms source_witness_decode_tail
#print axioms source_witness_decode_completed
#print axioms source_witness_decode_push
end InitECandidate.Runtime
