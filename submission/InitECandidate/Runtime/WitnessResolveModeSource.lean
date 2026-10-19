import InitECandidate.Runtime.DecodeWitnessNodeLoopSource
import InitECandidate.Runtime.ProgBounded
import InitECandidate.Runtime.GlobalsFrameComposition
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def witnessResolveCall : ProgHOL 64 :=
  match decodeWitnessNodeResolveMode with | .dec _ _ _ tail => tail | _ => .skip

def witnessResolveTail : ProgHOL 64 :=
  match witnessResolveCall with | .decCall _ _ _ _ tail => tail | _ => .skip

def witnessResolveArguments : List (ExpHOL 64) :=
  [.var .local (ofString "db"),
    .load .one (.op .add [.var .local (ofString "arr"),.panop .mul [.var .local (ofString "slot"),.const 16]]),
    .load .one (.op .add [.var .local (ofString "arr"),.panop .mul [.var .local (ofString "slot"),.const 16],.const 8])]

theorem source_witness_resolve_mode : decodeWitnessNodeResolveMode =
  .dec (ofString "arr") .one (.load .one (.op .add [.var .local (ofString "top"),.const 24])) witnessResolveCall := by
  simp only [witnessResolveCall,decodeWitnessNodeResolveMode,decodeWitnessNodeIteration,
    decodeWitnessNodeBodyAt,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_witness_resolve_call : witnessResolveCall =
  .decCall (ofString "r") (.comb [.one,.one,.one,.one]) (ofString "_resolve_step")
    witnessResolveArguments witnessResolveTail := by
  simp only [witnessResolveCall,witnessResolveTail,witnessResolveArguments,decodeWitnessNodeResolveMode,
    decodeWitnessNodeIteration,decodeWitnessNodeBodyAt,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_witness_resolve_tail : witnessResolveTail =
  .ite (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0))
    (.seq (.store (.op .add [.var .local (ofString "top"),.const 80]) (.const 0))
      (.seq (.assign .local (ofString "result") (.rfield 1 (.var .local (ofString "r"))))
        (.assign .local (ofString "mode") (.const 0))))
    (.seq (.store (.op .add [.var .local (ofString "top"),.const 80]) (.rfield 3 (.var .local (ofString "r"))))
      (.seq (.assign .local (ofString "cur_p") (.rfield 1 (.var .local (ofString "r"))))
        (.seq (.assign .local (ofString "cur_n") (.rfield 2 (.var .local (ofString "r"))))
          (.assign .local (ofString "mode") (.const 1))))) := by
  simp only [witnessResolveTail,witnessResolveCall,decodeWitnessNodeResolveMode,decodeWitnessNodeIteration,
    decodeWitnessNodeBodyAt,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Original post-resolver bookkeeping has zero source-clock cost even when
its store or local shape checks fail. -/
theorem witness_resolve_tail_bounded : ProgBounded witnessResolveTail 0 := by
  apply ProgBounded.straight
  rw [source_witness_resolve_tail]
  rfl

theorem witness_resolve_tail_globals_frame : OriginalGlobalsFrame witnessResolveTail := by
  apply originalGlobalsFrame_leaf
  intro watched
  rw [source_witness_resolve_tail]
  rfl

#print axioms source_witness_resolve_mode
#print axioms source_witness_resolve_call
#print axioms source_witness_resolve_tail
#print axioms witness_resolve_tail_bounded
#print axioms witness_resolve_tail_globals_frame
end InitECandidate.Runtime
