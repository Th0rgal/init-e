import InitECandidate.Runtime.StateInitJournalSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def decodeWitnessNodeBodyAt (n : Nat) : ProgHOL 64 :=
  stateInitSpineDrop n (sourceFunctionBody Guest.guestFn__decode_witness_node_body)

def decodeWitnessNodeIteration : ProgHOL 64 :=
  match decodeWitnessNodeBodyAt 7 with
  | .seq (.while _ iteration) _ => iteration
  | _ => .skip

def decodeWitnessNodeDecodeMode : ProgHOL 64 :=
  match decodeWitnessNodeIteration with | .ite _ body _ => body | _ => .skip

def decodeWitnessNodeResolveMode : ProgHOL 64 :=
  match decodeWitnessNodeIteration with | .ite _ _ (.ite _ body _) => body | _ => .skip

def decodeWitnessNodeUnwindMode : ProgHOL 64 :=
  match decodeWitnessNodeIteration with | .ite _ _ (.ite _ _ body) => body | _ => .skip

/-- The loop and its final return are the exact frozen source after the seven
initial local declarations. -/
theorem source_decode_witness_node_loop : decodeWitnessNodeBodyAt 7 =
    .seq (.while (.cmp .notEqual (.var .local (ofString "go")) (.const 0)) decodeWitnessNodeIteration)
      (.return (.var .local (ofString "result"))) := by
  unfold decodeWitnessNodeIteration decodeWitnessNodeBodyAt sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The actual explicit-stack iteration dispatches between decode, resolve and
unwind. Further rank proofs are about these original branches. -/
theorem source_decode_witness_node_modes : decodeWitnessNodeIteration =
    .ite (.cmp .equal (.var .local (ofString "mode")) (.const 1)) decodeWitnessNodeDecodeMode
      (.ite (.cmp .equal (.var .local (ofString "mode")) (.const 2)) decodeWitnessNodeResolveMode
        decodeWitnessNodeUnwindMode) := by
  unfold decodeWitnessNodeDecodeMode decodeWitnessNodeResolveMode decodeWitnessNodeUnwindMode
    decodeWitnessNodeIteration decodeWitnessNodeBodyAt sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_decode_witness_node_loop
#print axioms source_decode_witness_node_modes
end InitECandidate.Runtime
