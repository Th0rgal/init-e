import InitECandidate.Runtime.VersionedHashesBlobEntryBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Initializing the local blob cursor adds no source ticks to the loop bound. -/
theorem evaluate_versioned_hashes_blob_initialized_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count tx vh cursor : BitVec 64)
    (countLocal : state.locals.lookup (ofString "nb") = some (.val (.word count)))
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (vhLocal : state.locals.lookup (ofString "vh") = some (.val (.word vh)))
    (cursorLocal : state.locals.lookup (ofString "k") = some (.val (.word cursor)))
    (code : state.code = originalRuntimeCode) (budget : count.toNat * 130 ≤ state.clock) :
    let output := evaluateHOLFiniteState state (.dec (ofString "j") .one (.const 0) versionedHashesBlobLoop)
    state.clock ≤ output.2.clock + count.toNat * 130 ∧ output.2.clock ≤ state.clock ∧ output.1 ≠ some .timeOut := by
  let entry := setVarHOLFinite (ofString "j") (.val (.word 0)) state
  have indexLocal : entry.locals.lookup (ofString "j") = some (.val (.word 0)) := by
    simp [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have countEntry : entry.locals.lookup (ofString "nb") = some (.val (.word count)) := by
    simpa [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "j" ≠ ofString "nb" by decide] using countLocal
  have txEntry : entry.locals.lookup (ofString "tx") = some (.val (.word tx)) := by
    simpa [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "j" ≠ ofString "tx" by decide] using txLocal
  have vhEntry : entry.locals.lookup (ofString "vh") = some (.val (.word vh)) := by
    simpa [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "j" ≠ ofString "vh" by decide] using vhLocal
  have cursorEntry : entry.locals.lookup (ofString "k") = some (.val (.word cursor)) := by
    simpa [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "j" ≠ ofString "k" by decide] using cursorLocal
  have bounded := evaluate_versioned_hashes_blob_entry_bounded entry count tx vh cursor indexLocal countEntry txEntry vhEntry cursorEntry code budget
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
  exact bounded

theorem evaluate_versioned_hashes_blob_count_loaded_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count tx vh cursor : BitVec 64)
    (loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (.op .add [.var .local (ofString "tx"),.const 264])) = some (.val (.word count)))
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (vhLocal : state.locals.lookup (ofString "vh") = some (.val (.word vh)))
    (cursorLocal : state.locals.lookup (ofString "k") = some (.val (.word cursor)))
    (code : state.code = originalRuntimeCode) (budget : count.toNat * 130 ≤ state.clock) :
    let output := evaluateHOLFiniteState state (.dec (ofString "nb") .one (.load .one (.op .add [.var .local (ofString "tx"),.const 264]))
      (.dec (ofString "j") .one (.const 0) versionedHashesBlobLoop))
    state.clock ≤ output.2.clock + count.toNat * 130 ∧ output.2.clock ≤ state.clock ∧ output.1 ≠ some .timeOut := by
  let entry := setVarHOLFinite (ofString "nb") (.val (.word count)) state
  have countEntry : entry.locals.lookup (ofString "nb") = some (.val (.word count)) := by
    simp [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have txEntry : entry.locals.lookup (ofString "tx") = some (.val (.word tx)) := by
    simpa [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "nb" ≠ ofString "tx" by decide] using txLocal
  have vhEntry : entry.locals.lookup (ofString "vh") = some (.val (.word vh)) := by
    simpa [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "nb" ≠ ofString "vh" by decide] using vhLocal
  have cursorEntry : entry.locals.lookup (ofString "k") = some (.val (.word cursor)) := by
    simpa [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "nb" ≠ ofString "k" by decide] using cursorLocal
  have bounded := evaluate_versioned_hashes_blob_initialized_bounded entry count tx vh cursor countEntry txEntry vhEntry cursorEntry code budget
  rw [evaluateHOLFiniteState_dec_total]
  simp only [loaded,shapeOfHOLExact,shapeEqHOL,if_true]
  exact bounded


#print axioms evaluate_versioned_hashes_blob_count_loaded_bounded
#print axioms evaluate_versioned_hashes_blob_initialized_bounded
end InitECandidate.Runtime
