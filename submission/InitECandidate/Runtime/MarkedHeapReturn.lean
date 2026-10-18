import InitECandidate.Runtime.HeapReleaseReturned
import InitECandidate.Runtime.PanDiscardReturnGlobals
import InitECandidate.Runtime.PanDecReturnedScope
import InitECandidate.Runtime.PanDecCallReturnedContinuation
import InitECandidate.Runtime.NoDirectReturnWhile
import InitECandidate.Runtime.AvoidsLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A saved local mark survives the prefix, and every returned path reaches
the original heap-release call. Callees may have arbitrary global effects. -/
inductive MarkedHeapReturn (marker : MlS) : ProgHOL 64 → Prop
  | finish : MarkedHeapReturn marker
      (.seq (.call (some (none,none)) (ofString "heap_release") [.var .local marker]) (.return (.const 0)))
  | seq (first : ProgHOL 64) {tail : ProgHOL 64}
      (keeps : avoidsLocal marker first = true) (noReturn : noDirectReturnWhile first = true)
      (rest : MarkedHeapReturn marker tail) : MarkedHeapReturn marker (.seq first tail)
  | dec (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64) {body : ProgHOL 64}
      (different : name ≠ marker) (inner : MarkedHeapReturn marker body) :
      MarkedHeapReturn marker (.dec name shape initializer body)
  | decCall (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64))
      {continuation : ProgHOL 64} (different : name ≠ marker)
      (inner : MarkedHeapReturn marker continuation) :
      MarkedHeapReturn marker (.decCall name shape function arguments continuation)

theorem MarkedHeapReturn.returned {marker : MlS} {program : ProgHOL 64}
    (fragment : MarkedHeapReturn marker program) {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (mark : BitVec 64) (value : ValueHOL 64)
    (code : state.code = originalRuntimeCode)
    (saved : state.locals.lookup marker = some (.val (.word mark)))
    (run : evaluateHOLFiniteState state program = (some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word mark)) := by
  induction fragment generalizing state post with
  | finish =>
    obtain ⟨middle,called,globals⟩ := evaluate_discard_then_return_globals state post
      (ofString "heap_release") [.var .local marker] (.return (.const 0)) value (by rfl) run
    have released := heapRelease_call_normal state middle (.var .local marker) mark code
      (by simp [evalListHOLFinite_eq_toExact,evalListHOLExact,evalHOLExact,saved]) called
    rw [globals]
    exact released
  | seq first keeps noReturn rest ih =>
    obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
      (fun returnedValue => evaluate_noDirectReturnWhile first noReturn state returnedValue) run
    have frame := evaluate_avoidsLocal_flowing marker first keeps state (by rw [normal]; exact Or.inl rfl)
    have meta' := evaluateHOLFiniteState_metadata state first
    rw [normal] at frame meta'
    exact ih middle post (meta'.1.trans code) (frame.trans saved) tail
  | dec name shape initializer different inner ih =>
    obtain ⟨bound,output,_,bodyRun,postEq⟩ := evaluate_dec_returned_scope state post name shape initializer _ value run
    have atMarker : (setVarHOLFinite name bound state).locals.lookup marker = some (.val (.word mark)) := by
      simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different] using saved
    have result := ih (setVarHOLFinite name bound state) output code atMarker bodyRun
    rw [postEq]
    exact result
  | decCall name function shape arguments different inner ih =>
    obtain ⟨bound,ready,output,locals,installed,tail,globals⟩ :=
      evaluate_decCall_returned_continuation state post name function shape arguments _ value run
    have atMarker : (setVarHOLFinite name bound ready).locals.lookup marker = some (.val (.word mark)) := by
      simpa [setVarHOLFinite,locals,HolFiniteMapExact.lookup_update,FUPDATE,different] using saved
    rw [globals]
    exact ih (setVarHOLFinite name bound ready) output (installed.trans code) atMarker tail

#print axioms MarkedHeapReturn.returned
end InitECandidate.Runtime
