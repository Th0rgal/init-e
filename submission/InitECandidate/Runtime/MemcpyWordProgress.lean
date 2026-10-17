import InitECandidate.Runtime.WordAdvanceStep
import InitECandidate.Runtime.MemcpyWord32Step
import InitECandidate.Runtime.MemcpyWord8Loop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem memcpyWord8Body_supported : WordAdvanceStep (ofString "i") 8 memcpyWord8Body := by
  apply WordAdvanceStep.store
  exact WordAdvanceStep.advance

theorem evaluate_memcpy_word8_progress {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index : BitVec 64) (binding : state.locals.lookup (ofString "i") = some (.val (.word index))) :
    ∃ result post, evaluateHOLFiniteState state memcpyWord8Body = (result,post) ∧ post.clock = state.clock ∧
      (∀ name, name ≠ ofString "i" → post.locals.lookup name = state.locals.lookup name) ∧
      ((result = none ∧ post.locals.lookup (ofString "i") = some (.val (.word (index + 8)))) ∨ result = some .error) := by
  exact evaluate_wordAdvanceStep memcpyWord8Body_supported state index binding

#print axioms evaluate_memcpy_word8_progress
theorem memcpyWord32Body_supported : WordAdvanceStep (ofString "i") 32 memcpyWord32Body := by
  apply WordAdvanceStep.store
  apply WordAdvanceStep.store
  apply WordAdvanceStep.store
  apply WordAdvanceStep.store
  exact WordAdvanceStep.advance

theorem evaluate_memcpy_word32_progress {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index : BitVec 64) (binding : state.locals.lookup (ofString "i") = some (.val (.word index))) :
    ∃ result post, evaluateHOLFiniteState state memcpyWord32Body = (result,post) ∧ post.clock = state.clock ∧
      (∀ name, name ≠ ofString "i" → post.locals.lookup name = state.locals.lookup name) ∧
      ((result = none ∧ post.locals.lookup (ofString "i") = some (.val (.word (index + 32)))) ∨ result = some .error) := by
  exact evaluate_wordAdvanceStep memcpyWord32Body_supported state index binding

#print axioms evaluate_memcpy_word32_progress
end InitECandidate.Runtime
