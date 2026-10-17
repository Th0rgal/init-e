import InitECandidate.Runtime.RollbackPhysicalGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Resetting the journal needs no assumptions about stale saved records. The
new transaction starts with an empty typed prefix over its live table registry. -/
theorem rollback_reset_establishes_world {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64)) (journal snapshot oldCount : BitVec 64)
    (family : ∀ table ∈ tables, RollbackTableReady widths table state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (counterGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word oldCount)))
    (journalGlobal : state.globals.lookup (ofString "journal") = some (.val (.word journal)))
    (snapshotLocal : state.locals.lookup (ofString "snap") = some (.val (.word snapshot)))
    (layout : ∀ table ∈ tables, journal.toNat ≤ table.toNat) :
    ∃ post, evaluateHOLFiniteState state (.assign .global (ofString "journal_n") (.const 0)) = (none,post) ∧
      RollbackWorld widths tables journal snapshot 0 post ∧ RollbackPhysicalSeparated widths tables post ∧
      post.clock = state.clock ∧ post.locals = state.locals ∧ post.memory = state.memory ∧ post.memaddrs = state.memaddrs := by
  let post := setGlobalHOLFinite (ofString "journal_n") (.val (.word (0 : BitVec 64))) state
  have different : ofString "journal_n" ≠ ofString "journal" := by decide
  have valid : RollbackWorld widths tables journal snapshot 0 post := by
    refine ⟨?_,snapshotLocal,?_,by decide,?_,?_,?_,?_⟩
    · simp [post,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · simpa [post,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different] using journalGlobal
    · constructor
      · intro index inside
        change index < 0 at inside
        omega
      · intro index inside
        change index < 0 at inside
        omega
    · intro index inside
      change index < 0 at inside
      omega
    · intro table member
      obtain ⟨pointer,keys,stride,capacity,used,values,order,orderPos,items,bits,ready,small,big⟩ := family table member
      exact ⟨pointer,keys,stride,capacity,used,values,order,orderPos,items,bits,
        ready.after_global state (widths table) table pointer keys stride capacity used values order orderPos items bits
          (ofString "journal_n") (.val (.word (0 : BitVec 64))) (by decide),small,big⟩
    · intro table member
      simpa using layout table member
  refine ⟨post,?_,valid,separated.after_global (ofString "journal_n") (.val (.word (0 : BitVec 64))) (by decide),rfl,rfl,rfl,rfl⟩
  simp [evaluateHOLFiniteState_assign,evalHOLExact,isValidValueHOLExact,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite,lookupKvarHOLExact,counterGlobal,post]

#print axioms rollback_reset_establishes_world
end InitECandidate.Runtime
