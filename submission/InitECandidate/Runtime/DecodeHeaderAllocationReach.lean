import InitECandidate.Runtime.DecodeHeaderCountGuard
import InitECandidate.Runtime.AllocationDeclarationReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Initialization, accepted field count and the actual248-byte allocation
reach the first record store in2ticks or terminate earlier. Old memory is kept. -/
theorem decode_header_allocation_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count heap : BitVec 64) (code : s.code = originalRuntimeCode)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atCount : s.locals.lookup (ofString "n") = some (.val (.word count)))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (capped : heap.toNat ≤ 33806089496) (budget : 2 ≤ s.clock) :
    Reaches s (decodeHeaderAt 5)
      (fun post => ∃ flag : BitVec 64,
        ((count = 21 ∧ flag = 0) ∨ (count = 23 ∧ flag = 1)) ∧
        post.locals.lookup (ofString "arr") = some (.val (.word array)) ∧
        post.locals.lookup (ofString "n") = some (.val (.word count)) ∧
        post.locals.lookup (ofString "is_current") = some (.val (.word flag)) ∧
        post.locals.lookup (ofString "h") = some (.val (.word heap)) ∧
        post.memory = s.memory ∧ post.memaddrs = s.memaddrs ∧ post.code = s.code ∧
        post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd heap 248))) ∧
        (∀ name : MlS, name ≠ ofString "heap_ptr" → post.globals.lookup name = s.globals.lookup name) ∧
        heap.toNat + 248 ≤ (allocationEnd heap 248).toNat ∧
        (allocationEnd heap 248).toNat ≤ 33806089496 ∧ (allocationEnd heap 248).toNat % 8 = 0)
      2 (decodeHeaderAt 8) := by
  let initialized := setVarHOLFinite (ofString "is_current") (.val (.word (0#64))) s
  have start : Reaches s (decodeHeaderAt 5) (fun next => next = initialized) 0 (decodeHeaderAt 6) := by
    rw [source_decode_header_current]
    apply reaches_dec
    intro value evaluated
    have same : value = .val (.word (0#64)) := by simpa [evalHOLExact] using evaluated.symm
    subst value
    exact ⟨0,rfl,rfl⟩
  apply reaches_trans s (decodeHeaderAt 5) (decodeHeaderAt 6) (decodeHeaderAt 8) _ _ 0 2 start
  intro initial same
  subst initial
  have countKept : initialized.locals.lookup (ofString "n") = some (.val (.word count)) := by
    simpa (config := {decide := true}) [initialized,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atCount
  have flagZero : initialized.locals.lookup (ofString "is_current") = some (.val (.word (0#64))) := by
    simp [initialized,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  apply reaches_trans initialized (decodeHeaderAt 6) (decodeHeaderAt 7) (decodeHeaderAt 8) _ _ 0 2
    (decode_header_count_guard_reaches initialized count code countKept flagZero)
  intro checked facts
  have accepted : ∃ flag : BitVec 64,
      ((count = 21 ∧ flag = 0) ∨ (count = 23 ∧ flag = 1)) ∧
      checked.locals.lookup (ofString "arr") = some (.val (.word array)) ∧
      checked.locals.lookup (ofString "n") = some (.val (.word count)) ∧
      checked.locals.lookup (ofString "is_current") = some (.val (.word flag)) ∧
      checked.memory = s.memory ∧ checked.memaddrs = s.memaddrs ∧ checked.code = s.code ∧
      checked.globals = s.globals ∧ checked.clock = s.clock := by
    rcases facts with ⟨legacy,e⟩ | ⟨current,e⟩
    · subst checked
      refine ⟨0,Or.inl ⟨legacy,rfl⟩,?_,countKept,flagZero,rfl,rfl,rfl,rfl,rfl⟩
      simpa (config := {decide := true}) [initialized,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atArray
    · subst checked
      refine ⟨1,Or.inr ⟨current,rfl⟩,?_,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
      · simpa (config := {decide := true}) [initialized,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atArray
      · simpa (config := {decide := true}) [initialized,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atCount
      · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨flag,kind,arr,n,flagLocal,memory,domain,installed,globals,ticks⟩ := accepted
  rw [source_decode_header_allocation]
  have allocated := evaluate_allocation_declaration_reaches checked (.const 248) (ofString "h") heap 248
    (decodeHeaderAt 8) rfl (installed.trans code) (by rw [globals]; exact atHeap) capped (by rw [ticks]; exact budget)
  apply reaches_mono checked _ (decodeHeaderAt 8) _ _ 2 2 (le_refl _) ?_ allocated
  intro post allocation
  obtain ⟨locals,mem,ic,dom,glob,cap,extent,al⟩ := allocation
  refine ⟨flag,kind,?_,?_,?_,?_,mem.trans memory,dom.trans domain,ic.trans installed,?_,?_,?_,cap,al⟩
  · rw [locals]; simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using arr
  · rw [locals]; simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using n
  · rw [locals]; simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using flagLocal
  · rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
  · rw [glob]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro name different
    rw [glob]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,globals]
  · simpa using extent

#print axioms decode_header_allocation_reaches
end InitECandidate.Runtime
