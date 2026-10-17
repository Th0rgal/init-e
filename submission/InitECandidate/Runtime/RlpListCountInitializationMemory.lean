import InitECandidate.Runtime.RlpListCountInitialization
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem evaluate_rlpListCount_initialized_loop_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_list_count) = (result,post)) :
    ∃ output, evaluateHOLFiniteState (rlpListCountInitialState state) rlpListCountLoopAndReturn = (result,output) ∧
      post.memory = output.memory := by
  rw [source_rlpListCount_initialization] at run
  obtain ⟨first,firstRun,restore1⟩ := evaluate_dec_word_result_scope state post (ofString "count") (.const 0) 0 _ result (by rfl) run
  obtain ⟨output,bodyRun,restore2⟩ := evaluate_dec_word_result_scope _ first (ofString "off") (.const 0) 0 _ result (by rfl) firstRun
  refine ⟨output,bodyRun,?_⟩
  rw [restore1,restore2]


#print axioms evaluate_rlpListCount_initialized_loop_memory
end InitECandidate.Runtime
