import InitECandidate.Runtime.DecodeRequestsLoadsReturned
import InitECandidate.Runtime.DecodeRequestsAllocCheck
import InitECandidate.Runtime.AllocationReturnedGuard
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Request-array facts of a returned run after the offset check. -/
def ReqArrayFacts {σ : Type} (s : PanSemStateFiniteExact 64 σ) (p L pointer offsets : BitVec 64) (v : ValueHOL 64)
    (post : PanSemStateFiniteExact 64 σ) : Prop :=
  let O0 := memWord s.memory offsets
  let O1 := memWord s.memory (offsets + 8)
  let O2 := memWord s.memory (offsets + 16)
  let O3 := memWord s.memory (offsets + 24)
  let O4 := memWord s.memory (offsets + 32)
  let cells := reqCellValues p O0 O1 O2 O3 O4 ((O1 - O0) / 192) ((O2 - O1) / 76) ((O3 - O2) / 116)
    ((O4 - O3) / 184) ((L - O4) / 68)
  (80 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer ∧ v = .val (.word pointer) ∧
  s.memaddrs offsets ∧ s.memaddrs (offsets + 8) ∧ s.memaddrs (offsets + 16) ∧ s.memaddrs (offsets + 24) ∧
  s.memaddrs (offsets + 32) ∧
  (O1 - O0) % 192 = 0 ∧ (O2 - O1) % 76 = 0 ∧ (O3 - O2) % 116 = 0 ∧ (O4 - O3) % 184 = 0 ∧ (L - O4) % 68 = 0 ∧
  (∀ x ∈ cells, s.memaddrs (pointer + x.1)) ∧ post.memory = memWrites s.memory pointer cells ∧
  post.globals = (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word (allocationEnd pointer 80))) s).globals ∧
  post.memaddrs = s.memaddrs

theorem reqAlloc_returned {σ : Type} (s post : PanSemStateFiniteExact 64 σ) (p L pointer offsets : BitVec 64)
    (v : ValueHOL 64) (code : s.code = originalRuntimeCode)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word p)))
    (hL : s.locals.lookup (ofString "len") = some (.val (.word L)))
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496)
    (hg : s.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (run : evaluateHOLFiniteState s reqAlloc = (some (.returned v), post)) :
    ReqArrayFacts s p L pointer offsets v post := by
  have args : evalListHOLFinite s (h := fun address => Classical.propDecidable (s.memaddrs address))
      [.const 80] = some [.val (.word 80)] := by simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  unfold reqAlloc at run
  have request := alloc_declaration_returned_request s post _ pointer 80 (ofString "rq") .one reqLoads v args code heap run
  have zero : s.clock ≠ 0 := by
    intro z
    rw [evaluateHOLFiniteState_decCall_total, args] at run
    simp [z] at run
    split at run <;> simp at run
  obtain ⟨ready, _, _, rmem, rlocals, rcode, rdom, _, _, rglobals, decl⟩ :=
    evaluate_alloc_call_and_declaration s _ pointer 80 args code zero heap request
      (allocationEnd_within_heap pointer _ pointerBound request)
  rw [decl (ofString "rq") reqLoads] at run
  dsimp only at run
  generalize hr : setVarHOLFinite (ofString "rq") (.val (.word pointer)) ready = r at run
  cases inner : evaluateHOLFiniteState r reqLoads with
  | mk res out =>
    rw [inner] at run
    obtain ⟨r1, r2⟩ := Prod.mk.inj run
    dsimp only at r1 r2
    subst r1
    have hs : ofString "heap_ptr" ≠ ofString "ssz_offs" := by decide_cbv
    have lp : ofString "p" ≠ ofString "rq" := by decide_cbv
    have ll : ofString "len" ≠ ofString "rq" := by decide_cbv
    have facts := reqLoads_returned r out pointer p L offsets v (by rw [← hr]; exact rcode.trans code)
      (by rw [← hr]; simp [setVarHOLFinite, rglobals, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        hs, hg])
      (by rw [← hr]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      (by rw [← hr]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm lp, rlocals, hp])
      (by rw [← hr]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm ll, rlocals, hL]) inner
    have rm : r.memory = s.memory := by rw [← hr]; exact rmem
    have rd : r.memaddrs = s.memaddrs := by rw [← hr]; exact rdom
    have rg : r.globals = ready.globals := by rw [← hr]; rfl
    simp only [rm, rd, rg] at facts
    obtain ⟨d0, d1, d2, d3, d4, m0, m1, m2, m3, m4, hv, dom, mem, glob, dd⟩ := facts
    refine ⟨request, hv, d0, d1, d2, d3, d4, m0, m1, m2, m3, m4, dom, ?_, ?_, ?_⟩
    · rw [← r2]; exact mem
    · rw [← r2]; exact glob.trans rglobals
    · rw [← r2]; exact dd

#print axioms reqAlloc_returned
end InitECandidate.Runtime
