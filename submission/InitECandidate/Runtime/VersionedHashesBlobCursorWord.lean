import InitECandidate.Runtime.NormalWhileInvariant
import InitECandidate.Runtime.VersionedHashesBlobLocals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A normal blob traversal retains a word-valued shared cursor, without any
count-size, memory-domain or clock-reserve premise. -/
theorem versioned_hashes_blob_loop_cursor_word {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (cursor : BitVec 64)
    (binding : state.locals.lookup (ofString "k") = some (.val (.word cursor)))
    (run : evaluateHOLFiniteState state versionedHashesBlobLoop = (none,post)) :
    ∃ next : BitVec 64, post.locals.lookup (ofString "k") = some (.val (.word next)) := by
  let invariant := fun current : PanSemStateFiniteExact 64 F =>
    ∃ word : BitVec 64, current.locals.lookup (ofString "k") = some (.val (.word word))
  rw [source_versioned_hashes_blob_loop] at run
  apply evaluate_normal_while_invariant _ _ invariant ?_ ?_ ?_ state post ⟨cursor,binding⟩ run
  · rintro current ⟨word,localWord⟩
    exact ⟨word,localWord⟩
  · rintro current output ⟨word,localWord⟩ bodyRun
    exact ⟨word + 1,versioned_hashes_blob_step_k_adds_one current output word localWord bodyRun⟩
  · rw [source_versioned_hashes_blob_step]
    rfl

theorem normal_dec_cursor_word {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64) (body : ProgHOL 64)
    (different : name ≠ ofString "k")
    (child : ∀ current output : PanSemStateFiniteExact 64 F, ∀ word : BitVec 64,
      current.locals.lookup (ofString "k") = some (.val (.word word)) →
      evaluateHOLFiniteState current body = (none,output) →
      ∃ next : BitVec 64, output.locals.lookup (ofString "k") = some (.val (.word next)))
    (cursor : BitVec 64) (binding : state.locals.lookup (ofString "k") = some (.val (.word cursor)))
    (run : evaluateHOLFiniteState state (.dec name shape initializer body) = (none,post)) :
    ∃ next : BitVec 64, post.locals.lookup (ofString "k") = some (.val (.word next)) := by
  obtain ⟨value,output,_,bodyRun,scope⟩ := evaluate_dec_normal_scope state post name shape initializer body run
  have entered : (setVarHOLFinite name value state).locals.lookup (ofString "k") = some (.val (.word cursor)) := by
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different] using binding
  obtain ⟨next,word⟩ := child _ output cursor entered bodyRun
  refine ⟨next,?_⟩
  rw [scope]
  change (HolFiniteMapExact.resVarEq output.locals (name,state.locals.lookup name)).lookup (ofString "k") = _
  rw [restore_other_local _ name (ofString "k") _ (Ne.symm different)]
  exact word

theorem versioned_hashes_scan_cursor_word {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (cursor : BitVec 64) (binding : state.locals.lookup (ofString "k") = some (.val (.word cursor)))
    (run : evaluateHOLFiniteState state versionedHashesScan = (none,post)) :
    ∃ next : BitVec 64, post.locals.lookup (ofString "k") = some (.val (.word next)) := by
  rw [source_versioned_hashes_scan,evaluateHOLFiniteState_ite] at run
  split at run
  · split at run
    · rw [evaluateHOLFiniteState_skip] at run
      cases run
      exact ⟨cursor,binding⟩
    · apply normal_dec_cursor_word state post _ _ _ _ (by decide) ?_ cursor binding run
      intro current output word localWord childRun
      exact normal_dec_cursor_word current output _ _ _ _ (by decide)
        (fun entered final index atIndex loopRun => versioned_hashes_blob_loop_cursor_word entered final index atIndex loopRun)
        word localWord childRun
  · cases run

#print axioms normal_dec_cursor_word
#print axioms versioned_hashes_scan_cursor_word
#print axioms versioned_hashes_blob_loop_cursor_word
end InitECandidate.Runtime
