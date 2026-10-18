import InitECandidate.Runtime.VersionedHashesBlobLoopReadFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original conditional scan changes only locals on normal completion. -/
theorem versioned_hashes_scan_normal_read_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (tx vh cursor : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (vhLocal : state.locals.lookup (ofString "vh") = some (.val (.word vh)))
    (cursorLocal : state.locals.lookup (ofString "k") = some (.val (.word cursor)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state versionedHashesScan = (none,post)) :
    post.memory = state.memory ∧ post.globals = state.globals := by
  rw [source_versioned_hashes_scan,evaluateHOLFiniteState_ite] at run
  split at run
  · split at run
    · rw [evaluateHOLFiniteState_skip] at run
      cases run
      exact ⟨rfl,rfl⟩
    · obtain ⟨count,middle,_,childRun,outerScope⟩ := evaluate_dec_normal_scope state post _ _ _ _ run
      let entered := setVarHOLFinite (ofString "nb") count state
      obtain ⟨zero,output,initialized,loopRun,innerScope⟩ := evaluate_dec_normal_scope entered middle _ _ _ _ childRun
      have zeroEq : zero = .val (.word (0 : BitVec 64)) := by
        simpa only [evalHOLExact,Option.some.injEq] using initialized.symm
      subst zero
      let ready := setVarHOLFinite (ofString "j") (.val (.word (0 : BitVec 64))) entered
      have atJ : ready.locals.lookup (ofString "j") = some (.val (.word (0 : BitVec 64))) := by
        simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      have atTx : ready.locals.lookup (ofString "tx") = some (.val (.word tx)) := by
        simpa [ready,entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
          show ofString "j" ≠ ofString "tx" by decide,show ofString "nb" ≠ ofString "tx" by decide] using txLocal
      have atVh : ready.locals.lookup (ofString "vh") = some (.val (.word vh)) := by
        simpa [ready,entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
          show ofString "j" ≠ ofString "vh" by decide,show ofString "nb" ≠ ofString "vh" by decide] using vhLocal
      have atK : ready.locals.lookup (ofString "k") = some (.val (.word cursor)) := by
        simpa [ready,entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
          show ofString "j" ≠ ofString "k" by decide,show ofString "nb" ≠ ofString "k" by decide] using cursorLocal
      have frame := versioned_hashes_blob_loop_normal_read_frame ready output tx 0 vh cursor atTx atJ atVh atK code loopRun
      rw [outerScope,innerScope]
      exact frame
  · cases run

theorem versioned_hashes_scan_input_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (tx vh cursor array input inputLength : BitVec 64) (count : Nat)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (vhLocal : state.locals.lookup (ofString "vh") = some (.val (.word vh)))
    (cursorLocal : state.locals.lookup (ofString "k") = some (.val (.word cursor)))
    (code : state.code = originalRuntimeCode)
    (valid : RlpSliceInputPrefix state array input inputLength count)
    (run : evaluateHOLFiniteState state versionedHashesScan = (none,post)) :
    RlpSliceInputPrefix post array input inputLength count := by
  have frame := versioned_hashes_scan_normal_read_frame state post tx vh cursor txLocal vhLocal cursorLocal code run
  have metadata := evaluateHOLFiniteState_metadata state versionedHashesScan
  rw [run] at metadata
  intro index inside
  obtain ⟨pointer,length,entry⟩ := valid index inside
  exact ⟨pointer,length,RlpSliceInputEntry.after_frame state post array index pointer length input inputLength entry metadata.2.1
    (by rw [frame.1]) (by rw [frame.1])⟩

#print axioms versioned_hashes_scan_input_prefix
#print axioms versioned_hashes_scan_normal_read_frame
end InitECandidate.Runtime
