import InitECandidate.Runtime.RollbackWorldReset
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual reset-and-return suffix establishes the empty world with the
snapshot installed only in its logical entry state, not required in the caller. -/
theorem rollback_reset_return_establishes_world {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64)) (journal snapshot oldCount : BitVec 64)
    (family : ∀ table ∈ tables, RollbackTableReady widths table state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (counterGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word oldCount)))
    (journalGlobal : state.globals.lookup (ofString "journal") = some (.val (.word journal)))
    (layout : ∀ table ∈ tables, journal.toNat ≤ table.toNat) :
    ∃ post, evaluateHOLFiniteState state (.seq (.assign .global (ofString "journal_n") (.const 0)) (.return (.const 0))) =
      (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite post) ∧
      RollbackWorld widths tables journal snapshot 0 (setVarHOLFinite (ofString "snap") (.val (.word snapshot)) post) ∧
      RollbackPhysicalSeparated widths tables post ∧ post.clock = state.clock ∧ post.memaddrs = state.memaddrs := by
  let bound := setVarHOLFinite (ofString "snap") (.val (.word snapshot)) state
  let post := setGlobalHOLFinite (ofString "journal_n") (.val (.word (0 : BitVec 64))) state
  obtain ⟨checked,run,world,_,_,_,_,_⟩ := rollback_reset_establishes_world bound widths tables journal snapshot oldCount
    (fun table member => (family table member).after_read rfl rfl rfl rfl rfl)
    (separated.after_read (after := bound) rfl rfl rfl rfl rfl) counterGlobal journalGlobal
    (by simp [bound,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) layout
  have canonical : evaluateHOLFiniteState bound (.assign .global (ofString "journal_n") (.const 0)) =
      (none,setVarHOLFinite (ofString "snap") (.val (.word snapshot)) post) := by
    simp [evaluateHOLFiniteState_assign,evalHOLExact,isValidValueHOLExact,shapeOfHOLExact,shapeEqHOL,
      setKvarHOLFinite,lookupKvarHOLExact,counterGlobal,bound,post,setVarHOLFinite,setGlobalHOLFinite]
  have same : checked = setVarHOLFinite (ofString "snap") (.val (.word snapshot)) post := congrArg Prod.snd (run.symm.trans canonical)
  rw [same] at world
  have reset : evaluateHOLFiniteState state (.assign .global (ofString "journal_n") (.const 0)) = (none,post) := by
    simp [evaluateHOLFiniteState_assign,evalHOLExact,isValidValueHOLExact,shapeOfHOLExact,shapeEqHOL,
      setKvarHOLFinite,lookupKvarHOLExact,counterGlobal,post]
  refine ⟨post,?_,world,separated.after_global (ofString "journal_n") (.val (.word (0 : BitVec 64))) (by decide),rfl,rfl⟩
  rw [evaluateHOLFiniteState_seq_line780,reset]
  simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]

#print axioms rollback_reset_return_establishes_world
end InitECandidate.Runtime
