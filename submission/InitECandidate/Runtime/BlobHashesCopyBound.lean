import InitECandidate.Runtime.MemcpyCallBound
import InitECandidate.Runtime.BlobHashesSource
import InitECandidate.Runtime.StraightLineNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def blobHashesCopyTail : ProgHOL 64 :=
  match blobHashesStep with | .decCall _ _ _ _ body => body | _ => .skip

theorem source_blobHashes_copy_tail : blobHashesCopyTail =
    .seq (.call (some (none,none)) (ofString "memcpy")
      [.op .add [.var .local (ofString "buf"),.panop .mul [.var .local (ofString "i"),.const 32]],
       .var .local (ofString "h"),.const 32])
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])) := by
  unfold blobHashesCopyTail
  rw [source_blobHashes_step]

/-- The actual blob-hash copy and counter update use at most sixteen clocks,
including unaligned or inaccessible memory and all copy errors. -/
theorem evaluate_blobHashes_copy_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (buffer index source : BitVec 64)
    (bufferLocal : state.locals.lookup (ofString "buf") = some (.val (.word buffer)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (sourceLocal : state.locals.lookup (ofString "h") = some (.val (.word source)))
    (code : state.code = originalRuntimeCode) (budget : 16 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state blobHashesCopyTail
    state.clock ≤ evaluated.2.clock + 16 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let arguments : List (ExpHOL 64) :=
    [.op .add [.var .local (ofString "buf"),.panop .mul [.var .local (ofString "i"),.const 32]],.var .local (ofString "h"),.const 32]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word (buffer + index * 32)),.val (.word source),.val (.word (32 : BitVec 64))] := by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,bufferLocal,indexLocal,sourceLocal,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord]
  have bounded := evaluate_memcpy_call_bounded state arguments (buffer + index * 32) source 32 args code (by decide) budget
  cases run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "memcpy") arguments) with
  | mk result middle =>
    rw [run] at bounded
    dsimp only at bounded
    rw [source_blobHashes_copy_tail,evaluateHOLFiniteState_seq_line780]
    change (let evaluated := (match evaluateHOLFiniteState state (.call (some (none,none)) (ofString "memcpy") arguments) with
      | (none,next) => evaluateHOLFiniteState next (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1]))
      | stopped => stopped); _) 
    rw [run]
    cases result with
    | some stopped => exact bounded
    | none =>
      have clock := clockPreserving_assign (σ := F) .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1]) middle
      have safe := evaluate_straightLine_no_timeout (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])) (by rfl) middle
      exact ⟨by dsimp only; rw [clock]; exact bounded.1,by dsimp only; rw [clock]; exact bounded.2.1,safe⟩

#print axioms evaluate_blobHashes_copy_bounded
end InitECandidate.Runtime
