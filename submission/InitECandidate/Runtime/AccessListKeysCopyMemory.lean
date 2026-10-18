import InitECandidate.Runtime.MemcpyCallMemory
import InitECandidate.Runtime.AccessListKeysCopyBound
import InitECandidate.Runtime.ReadOnlyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful copy and index increment preserve memory outside the copied cells. -/
theorem access_keys_copy_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (buffer index source watched : BitVec 64)
    (bufferLocal : state.locals.lookup (ofString "keys") = some (.val (.word buffer)))
    (indexLocal : state.locals.lookup (ofString "j") = some (.val (.word index)))
    (sourceLocal : state.locals.lookup (ofString "k") = some (.val (.word source)))
    (code : state.code = originalRuntimeCode)
    (wordSeparate : ∀ offset : Nat, offset < 32 → watched ≠ (buffer + index * 32) + BitVec.ofNat 64 offset)
    (byteSeparate : ∀ offset : Nat, offset < 32 → watched ≠ panByteAlignHOL ((buffer + index * 32) + BitVec.ofNat 64 offset))
    (budget : 16 ≤ state.clock)
    (run : evaluateHOLFiniteState state accessKeysCopy = (none,post)) :
    post.memory watched = state.memory watched := by
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
      have frame := memcpy_call_normal_memory state middle arguments (buffer + index * 32) source 32 watched args code
        wordSeparate byteSeparate (by decide) budget copied
      have retained := evaluate_readOnly_memory
        (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"),.const 1])) (by rfl) middle
      dsimp only at run
      rw [run] at retained
      exact (congrFun retained watched).trans frame

#print axioms access_keys_copy_normal_memory
end InitECandidate.Runtime
