import InitECandidate.Runtime.MemcpyGlobals
import InitECandidate.Runtime.AccessListKeysCopyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful copy and index increment preserve all runtime globals. -/
theorem access_keys_copy_normal_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (buffer index source : BitVec 64)
    (bufferLocal : state.locals.lookup (ofString "keys") = some (.val (.word buffer)))
    (indexLocal : state.locals.lookup (ofString "j") = some (.val (.word index)))
    (sourceLocal : state.locals.lookup (ofString "k") = some (.val (.word source)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state accessKeysCopy = (none,post)) :
    post.globals = state.globals := by
  let arguments : List (ExpHOL 64) :=
    [.op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "j"),.const 32]],.var .local (ofString "k"),.const 32]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word (buffer + index * 32)),.val (.word source),.val (.word (32 : BitVec 64))] := by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,bufferLocal,indexLocal,sourceLocal,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord]
  rw [source_access_keys_copy,evaluateHOLFiniteState_seq_line780] at run
  cases copied : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "memcpy") arguments) with
  | mk result middle =>
    have copiedExpanded := copied
    dsimp only [arguments] at copiedExpanded
    rw [copiedExpanded] at run
    cases result with
    | some stopped => cases run
    | none =>
      have frame := memcpy_call_normal_globals state middle arguments (buffer + index * 32) source 32 args code copied
      apply HolFiniteMapExact.ext
      funext watched
      have retained := evaluate_avoidsGlobalAssignment watched
        (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"),.const 1])) (by rfl) middle
      dsimp only at run
      rw [run] at retained
      exact retained.trans (congrArg (fun g => g.lookup watched) frame)

#print axioms access_keys_copy_normal_globals
end InitECandidate.Runtime
