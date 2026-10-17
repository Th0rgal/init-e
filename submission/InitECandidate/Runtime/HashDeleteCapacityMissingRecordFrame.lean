import InitECandidate.Runtime.HashDeleteCapacityScopeMetadataSupported
import InitECandidate.Runtime.JournalUndoRecordsRead
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableArraysInvariant.delete_capacity_scope_with_record_frame_missing_width {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos items : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits state)
    (linked : HashOrderLinked used order orderPos capacity items state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word capacity)))
    (journal : BitVec 64) (journalCount : Nat)
 :
    ∃ post, evaluateHOLFiniteState state (.dec (ofString "cap") .one (.load .one (hashLocalAddress (ofString "t") 16))
        (.seq hashDeleteMissingGuard hashDeleteFoundHeaderScopes)) = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      (∀ index : Nat, index < journalCount → ∀ offset ∈ ([0,8,16,24] : List Nat),
        post.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) =
          state.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset)) ∧
      post.clock = state.clock ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  let entered := setVarHOLFinite (ofString "cap") (.val (.word capacity)) state
  have different : ofString "cap" ≠ ofString "i" := by decide
  have iLocal : entered.locals.lookup (ofString "i") = some (.val (.word capacity)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different] using indexLocal
  have capLocal : entered.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have domains := invariant.header_domain state keyLength table keys stride capacity used values order orderPos items bits
  rw [evaluate_header_load_scope state (ofString "cap") (ofString "t") table 16 capacity _ tableLocal (domains 16 (by decide)) invariant.cell16]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780,evaluate_hashDelete_guard_missing entered capacity iLocal capLocal]
  exact ⟨_,rfl,(by intro index inside offset member; rfl),rfl,rfl,rfl,rfl,rfl⟩

#print axioms HashTableArraysInvariant.delete_capacity_scope_with_record_frame_missing_width
end InitECandidate.Runtime
