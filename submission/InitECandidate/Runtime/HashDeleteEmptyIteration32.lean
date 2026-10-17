import InitECandidate.Runtime.HashDeleteOccupiedIteration32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The terminating iteration advances the scan and breaks with all table
facts intact, consuming no body clock beyond the while entry. -/
theorem evaluate_hashDelete_empty_allocated_iteration32 {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos items index : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos items bits state)
    (entries : HashValueEntriesWord used values capacity state)
    (reverse : HashReverseEntriesBound used orderPos capacity items state)
    (ordered : HashOrderEntriesBound order capacity items state)
    (indexLocal : state.locals.lookup (ofString "j") = some (.val (.word index)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (empty : hashOccupancyRead state used (hashProbeNext index capacity) = some 0) :
    ∃ post, evaluateHOLFiniteState state hashDeleteLoopBody = (some .break,post) ∧
      post.clock = state.clock ∧
      HashTableArraysInvariant32 table keys stride capacity used values order orderPos items bits post ∧
      HashValueEntriesWord used values capacity post ∧ HashReverseEntriesBound used orderPos capacity items post ∧
      HashOrderEntriesBound order capacity items post ∧
      post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      post.locals.lookup (ofString "j") = some (.val (.word (hashProbeNext index capacity))) ∧
      (∀ name, name ≠ ofString "j" → post.locals.lookup name = state.locals.lookup name) := by
  let post := setVarHOLFinite (ofString "j") (.val (.word (hashProbeNext index capacity))) state
  have run := evaluate_hashDelete_empty_iteration state index capacity used indexLocal capacityLocal usedLocal empty
  refine ⟨post,run,rfl,
    invariant.after_read state post table keys stride capacity used values order orderPos items bits rfl rfl rfl rfl,
    entries.after_read state post used values capacity rfl rfl rfl,
    reverse.after_read state post used orderPos capacity items rfl rfl rfl,
    ordered.after_memory state post order capacity items rfl,rfl,rfl,rfl,rfl,rfl,?_,?_⟩
  · simp [post,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro name different
    simp [post,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]

#print axioms evaluate_hashDelete_empty_allocated_iteration32
end InitECandidate.Runtime
