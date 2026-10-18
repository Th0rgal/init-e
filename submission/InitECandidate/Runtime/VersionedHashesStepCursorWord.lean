import InitECandidate.Runtime.VersionedHashesBlobCursorWord
import InitECandidate.Runtime.NormalDecCallLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem normal_decCall_cursor_word {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) (body : ProgHOL 64)
    (different : name ≠ ofString "k")
    (child : ∀ current output : PanSemStateFiniteExact 64 F, ∀ word : BitVec 64,
      current.locals.lookup (ofString "k") = some (.val (.word word)) →
      evaluateHOLFiniteState current body = (none,output) →
      ∃ next : BitVec 64, output.locals.lookup (ofString "k") = some (.val (.word next)))
    (cursor : BitVec 64) (binding : state.locals.lookup (ofString "k") = some (.val (.word cursor)))
    (run : evaluateHOLFiniteState state (.decCall name shape function arguments body) = (none,post)) :
    ∃ next : BitVec 64, post.locals.lookup (ofString "k") = some (.val (.word next)) := by
  obtain ⟨value,ready,output,locals,bodyRun,scope⟩ :=
    evaluate_decCall_unconditional_normal_scope state post name function shape arguments body run
  have entered : (setVarHOLFinite name value ready).locals.lookup (ofString "k") = some (.val (.word cursor)) := by
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,locals] using binding
  obtain ⟨next,word⟩ := child _ output cursor entered bodyRun
  refine ⟨next,?_⟩
  rw [scope]
  change (HolFiniteMapExact.resVarEq output.locals (name,state.locals.lookup name)).lookup (ofString "k") = _
  rw [restore_other_local _ name (ofString "k") _ (Ne.symm different)]
  exact word

/-- Normal execution of the original outer validation step retains a typed
shared hash cursor, even though each called helper has private locals. -/
theorem versioned_hashes_step_cursor_word {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (cursor : BitVec 64) (binding : state.locals.lookup (ofString "k") = some (.val (.word cursor)))
    (run : evaluateHOLFiniteState state versionedHashesStep = (none,post)) :
    ∃ next : BitVec 64, post.locals.lookup (ofString "k") = some (.val (.word next)) := by
  rw [source_versioned_hashes_step] at run
  apply normal_decCall_cursor_word state post _ _ _ _ _ (by decide) ?_ cursor binding run
  intro current output word localWord childRun
  apply normal_decCall_cursor_word current output _ _ _ _ _ (by decide) ?_ word localWord childRun
  intro entered final index atIndex tailRun
  rw [evaluateHOLFiniteState_seq_line780] at tailRun
  cases scanned : evaluateHOLFiniteState entered versionedHashesScan with
  | mk result middle =>
    rw [scanned] at tailRun
    cases result with
    | some result => cases tailRun
    | none =>
      dsimp only at tailRun
      obtain ⟨next,word⟩ := versioned_hashes_scan_cursor_word entered middle index atIndex scanned
      have kept := evaluate_straight_local_frame (ofString "k")
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])) (by decide) middle
      rw [tailRun] at kept
      exact ⟨next,kept.trans word⟩

#print axioms normal_decCall_cursor_word
#print axioms versioned_hashes_step_cursor_word
end InitECandidate.Runtime
