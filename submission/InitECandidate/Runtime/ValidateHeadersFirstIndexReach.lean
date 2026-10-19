import InitECandidate.Runtime.ValidateHeadersFirstLoopReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Concrete state before the source declares its loop index. No pre-existing
binding for i is required. -/
def ValidateHeadersFirstReady {F : Type} (e : ValidateHeadersFirstEnvironment)
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ heap : BitVec 64,
    s.locals.lookup (ofString "arr") = some (.val (.word e.array)) ∧
    s.locals.lookup (ofString "n") = some (.val (.word e.count)) ∧
    s.locals.lookup (ofString "hs") = some (.val (.word e.hs)) ∧
    s.locals.lookup (ofString "hashes") = some (.val (.word e.hashes)) ∧
    RlpSliceInputPrefix s e.array e.input e.inputLength e.count.toNat ∧
    e.input.toNat + e.inputLength.toNat ≤ heap.toNat ∧
    e.array.toNat + e.count.toNat * 16 ≤ heap.toNat ∧
    s.globals.lookup (ofString "scratch_ptr") = some (.val (.word e.scratch)) ∧
    s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word e.frame)) ∧
    s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
    s.globals.lookup (ofString "keccak_st") = some (.val (.word e.keccakState)) ∧
    s.globals.lookup (ofString "keccak_pad") = some (.val (.word e.keccakPad)) ∧
    heap.toNat ≤ 33806089496 ∧
    (∀ address : BitVec 64, e.frame.toNat ≤ address.toNat → address.toNat < e.ceiling → s.memaddrs address) ∧
    (∀ address : BitVec 64, heap.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)

/-- Initializing the actual local counter establishes the checked invariant. -/
theorem validate_headers_first_index_invariant {F : Type} (e : ValidateHeadersFirstEnvironment)
    (s : PanSemStateFiniteExact 64 F) (ready : ValidateHeadersFirstReady e s) :
    ValidateHeadersFirstInvariant e (setVarHOLFinite (ofString "i") (.val (.word 0)) s) e.count.toNat := by
  obtain ⟨heap,arr,n,hs,hashes,table,rest⟩ := ready
  refine ⟨0,heap,?_,?_,?_,?_,?_,by simp,by simp,?_,rest⟩
  · simpa (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using arr
  · simpa (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using n
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simpa (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using hs
  · simpa (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using hashes
  · intro slot inside
    obtain ⟨pointer,length,entry⟩ := table slot inside
    exact ⟨pointer,length,entry.after_frame s _ e.array slot pointer length e.input e.inputLength rfl rfl rfl⟩

/-- The exact index declaration reaches the bounded first-loop continuation
at zero source ticks, preserving the concrete memory premises. -/
theorem validate_headers_first_index_reaches {F : Type} (e : ValidateHeadersFirstEnvironment)
    (s : PanSemStateFiniteExact 64 F) (ready : ValidateHeadersFirstReady e s) :
    Reaches s (validateHeadersAt 3)
      (fun post => ValidateHeadersFirstInvariant e post e.count.toNat ∧ post.code = s.code)
      0 (validateHeadersAt 4) := by
  rw [source_validate_headers_index_init]
  apply reaches_dec
  intro value initialized
  have same : value = .val (.word (0 : BitVec 64)) := by
    simpa [evalHOLExact] using initialized.symm
  subst value
  exact ⟨0,rfl,validate_headers_first_index_invariant e s ready,rfl⟩

#print axioms validate_headers_first_index_invariant
#print axioms validate_headers_first_index_reaches
end InitECandidate.Runtime
