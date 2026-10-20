import InitECandidate.Runtime.DecodeWitnessNodeLoopSource
import InitECandidate.Runtime.RunBounded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- The seven initializer declarations are the exact original source. -/
theorem source_decode_witness_node_entry : sourceFunctionBody Guest.guestFn__decode_witness_node_body =
    .dec (ofString "top") .one (.const 0)
    (.dec (ofString "result") .one (.const 0)
    (.dec (ofString "cur_p") .one (.var .local (ofString "p"))
    (.dec (ofString "cur_n") .one (.var .local (ofString "n"))
    (.dec (ofString "mode") .one (.const 1)
    (.dec (ofString "slot") .one (.const 0)
    (.dec (ofString "go") .one (.const 1) (decodeWitnessNodeBodyAt 7))))))) := by
  unfold decodeWitnessNodeBodyAt sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl
/-- Actual local values on entering the original loop. -/
def witnessTraversalEntry {F : Type} (s : PanSemStateFiniteExact 64 F) (pointer length : BitVec 64) :
    PanSemStateFiniteExact 64 F :=
  setVarHOLFinite (ofString "go") (.val (.word (1#64)))
  (setVarHOLFinite (ofString "slot") (.val (.word (0#64)))
  (setVarHOLFinite (ofString "mode") (.val (.word (1#64)))
  (setVarHOLFinite (ofString "cur_n") (.val (.word length))
  (setVarHOLFinite (ofString "cur_p") (.val (.word pointer))
  (setVarHOLFinite (ofString "result") (.val (.word (0#64)))
  (setVarHOLFinite (ofString "top") (.val (.word (0#64))) s))))))
#print axioms source_decode_witness_node_entry
end InitECandidate.Runtime
