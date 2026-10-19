import InitECandidate.Runtime.Sha256PairSource
import InitECandidate.Runtime.Sha256FinishMemory
import InitECandidate.Runtime.PanDiscardReturnMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The final original SHA-pair suffix writes only the aligned output region. -/
theorem shaPair_finish_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer out watched : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (aligned : out.toNat % 8 = 0) (fits : out.toNat + 32 ≤ 33806089496)
    (outside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (shaPairAt 8) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  rw [source_shaPair_finish,source_shaPair_return] at run
  obtain ⟨middle,normal,memory⟩ := evaluate_discard_then_return_memory state post (ofString "sha256_finish")
    _ (.return (.const 0)) value rfl run
  have frame := shaFinish_call_normal_memory state middle _ pointer out watched
    (by simp [evalListHOLExact,evalHOLExact,atPointer,atOut]) aligned fits outside code normal
  exact (congrFun memory watched).trans frame

#print axioms shaPair_finish_returned_memory
end InitECandidate.Runtime
