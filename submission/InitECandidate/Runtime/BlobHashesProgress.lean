import InitECandidate.Runtime.BlobHashesSource
import InitECandidate.Runtime.DiscardCallSuccessLocals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def blobHashesCopyAndAdvance : ProgHOL 64 :=
  match blobHashesStep with | .decCall _ _ _ _ body => body | _ => .skip

theorem source_blobHashes_copy_and_advance : blobHashesCopyAndAdvance =
    .seq (.call (some (none,none)) (ofString "memcpy")
      [.op .add [.var .local (ofString "buf"),.panop .mul [.var .local (ofString "i"),.const 32]],
       .var .local (ofString "h"),.const 32])
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])) := by
  rw [blobHashesCopyAndAdvance,source_blobHashes_step]

/-- Any normally completed original copy/advance suffix increments i and
preserves the slice pair, regardless of the callee's memory effects. -/
theorem blobHashes_copy_normal_progress {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (index count array : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (listLocal : state.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)]))
    (enabled : index.toNat < count.toNat)
    (run : evaluateHOLFiniteState state blobHashesCopyAndAdvance = (none,post)) :
    post.locals.lookup (ofString "i") = some (.val (.word (index + 1))) ∧
    post.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)]) ∧
    (index + 1).toNat ≤ count.toNat ∧ count.toNat - (index + 1).toNat < count.toNat - index.toNat := by
  let arguments : List (ExpHOL 64) :=
    [.op .add [.var .local (ofString "buf"),.panop .mul [.var .local (ofString "i"),.const 32]],
     .var .local (ofString "h"),.const 32]
  rw [source_blobHashes_copy_and_advance,evaluateHOLFiniteState_seq_line780] at run
  cases copied : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "memcpy") arguments) with
  | mk result middle =>
    dsimp only [arguments] at copied
    rw [copied] at run
    cases result with
    | some stopped => cases run
    | none =>
      have locals := evaluate_discard_call_success_locals state (ofString "memcpy") arguments (by rw [copied])
      rw [copied] at locals
      dsimp only at locals
      have atIndex := locals ▸ indexLocal
      have advanced : evaluateHOLFiniteState middle (.assign .local (ofString "i")
          (.op .add [.var .local (ofString "i"),.const 1])) =
          (none,setVarHOLFinite (ofString "i") (.val (.word (index + 1))) middle) := by
        simp [evaluateHOLFiniteState_assign,evalHOLExact,evalListHOLExact,atIndex,
          lookupKvarHOLExact,isValidValueHOLExact,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite,wordOpHOL,wordOp,valueIsWord,valueWord]
      have postEq := (Prod.mk.inj (run.symm.trans advanced)).2
      rw [postEq]
      have progress := rlpSlices_index_progress index count enabled
      refine ⟨?_,?_,progress.2⟩
      · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
          show ofString "i" ≠ ofString "lst" by decide] using listLocal

#print axioms blobHashes_copy_normal_progress
end InitECandidate.Runtime
