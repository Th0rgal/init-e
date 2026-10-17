import InitECandidate.Runtime.RlpHeaderLongStringReturnedMemory
import InitECandidate.Runtime.RlpHeaderLongStringContract
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful long-header execution passes the availability check without
changing memory before its checked length-reader continuation. -/
theorem rlpHeader_long_string_body_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer lengthBytes : BitVec 64) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "ll") = some (.val (.word lengthBytes)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state rlpHeaderLongStringBody = (some (.returned value),post)) :
    post.memory = state.memory := by
  obtain ⟨result,middle,check,normal,noReturn⟩ := evaluate_rlp_error_check_flow state
    (.cmp .lower (.op .sub [.var .local (ofString "len"),.const 1]) (.var .local (ofString "ll"))) 3 code
  rw [source_rlpHeader_long_string_body,evaluateHOLFiniteState_seq_line780,check] at run
  cases result with
  | some stopped => exact False.elim (noReturn value (Prod.mk.inj run).1)
  | none =>
    have same := normal rfl
    subst middle
    exact rlpHeader_long_string_read_returned_memory state post pointer lengthBytes value pointerLocal lengthLocal code run

/-- The original long-string header declaration preserves caller memory on
successful return, including restoration of the length-of-length local. -/
theorem rlpHeader_long_string_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer header : BitVec 64) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state rlpHeaderLongString = (some (.returned value),post)) :
    post.memory = state.memory := by
  have initial : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .sub [.var .local (ofString "b"),.const 183]) = some (.val (.word (header - 183))) := by
    simp [evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_rlpHeader_long_string] at run
  obtain ⟨output,bodyRun,restored⟩ := evaluate_dec_word_result_scope state post (ofString "ll")
    (.op .sub [.var .local (ofString "b"),.const 183]) (header - 183) rlpHeaderLongStringBody (some (.returned value)) initial run
  let entered := setVarHOLFinite (ofString "ll") (.val (.word (header - 183))) state
  have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "ll" ≠ ofString "p" by decide] using pointerLocal
  have atLength : entered.locals.lookup (ofString "ll") = some (.val (.word (header - 183))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have memory := rlpHeader_long_string_body_returned_memory entered output pointer (header - 183) value
    atPointer atLength code bodyRun
  rw [restored]
  exact memory

#print axioms rlpHeader_long_string_body_returned_memory
#print axioms rlpHeader_long_string_returned_memory
end InitECandidate.Runtime
