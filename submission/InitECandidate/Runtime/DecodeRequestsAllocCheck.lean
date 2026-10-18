import InitECandidate.Runtime.DecodeRequestsLoads
import InitECandidate.Runtime.DecodeRequestsCheckCall
import InitECandidate.Runtime.AllocationCall
import InitECandidate.Runtime.AllocationBodyBound
import InitECandidate.Runtime.AllocationFailureDeclaration
import InitECandidate.Runtime.AllocationFailureDeclarationNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def ReqAllocPre {σ : Type} (t : PanSemStateFiniteExact 64 σ) : Prop :=
  t.code = originalRuntimeCode ∧ (∃ L : BitVec 64, t.locals.lookup (ofString "len") = some (.val (.word L))) ∧
    ∃ pointer : BitVec 64, t.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)) ∧
      pointer.toNat ≤ 33806089496

theorem reqAlloc_bounded {σ : Type} : ReqBounded (σ := σ) ReqAllocPre reqAlloc 337 := by
  rintro t ⟨code, ⟨L, hL⟩, pointer, heap, pointerBound⟩ enough
  have args : evalListHOLFinite t (h := fun address => Classical.propDecidable (t.memaddrs address))
      [.const 80] = some [.val (.word 80)] := by simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  unfold reqAlloc
  by_cases request : (80 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer
  · obtain ⟨ready, _, rclock, _, rlocals, rcode, _, _, _, _, decl⟩ :=
      evaluate_alloc_call_and_declaration t _ pointer 80 args code (by omega) heap request
        (allocationEnd_within_heap pointer _ pointerBound request)
    rw [decl (ofString "rq") reqLoads]
    dsimp only
    have rq : ofString "len" ≠ ofString "rq" := by decide_cbv
    generalize hr : setVarHOLFinite (ofString "rq") (.val (.word pointer)) ready = r
    have rc : r.clock = t.clock - 1 := by rw [← hr]; exact rclock
    obtain ⟨b1, b2, b3⟩ := reqLoads_bounded r
      ⟨by rw [← hr]; exact rcode.trans code, L, by
        rw [← hr]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, rq, Ne.symm rq, rlocals, hL]⟩
      (by omega)
    exact ⟨by omega, by omega, b3⟩
  · have over : ((33806089496 : BitVec 64) - pointer).toNat < (80 : BitVec 64).toNat := by
      rw [BitVec.le_def] at request; omega
    have f1 := evaluate_alloc_request_failure_declaration t _ pointer 80 (ofString "rq") .one reqLoads args code heap over
    have f2 := evaluate_alloc_request_failure_declaration_no_timeout t _ pointer 80 (ofString "rq") .one reqLoads
      args code heap over (by omega)
    exact ⟨by omega, by omega, f2⟩

def ReqCheckPre {σ : Type} (t : PanSemStateFiniteExact 64 σ) : Prop :=
  ReqAllocPre t ∧ ∃ offsets : BitVec 64, t.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets))

theorem reqCheckAlloc_bounded {σ : Type} : ReqBounded (σ := σ) ReqCheckPre (.seq reqCheck reqAlloc) 349 := by
  rintro t ⟨⟨code, ⟨L, hL⟩, pointer, heap, pointerBound⟩, offsets, hg⟩ enough
  obtain ⟨c1, c2, c3⟩ := reqCheck_bounded t offsets L hg hL code (by omega)
  rw [evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState t reqCheck with
  | mk result post =>
    rw [run] at c1 c2 c3
    dsimp only at c1 c2 c3 ⊢
    cases result with
    | none =>
      dsimp only
      obtain ⟨_, pl, _, pg, _, pc⟩ := reqCheck_normal t post offsets L hg hL code run
      obtain ⟨a1, a2, a3⟩ := reqAlloc_bounded post
        ⟨pc.trans code, ⟨L, by rw [pl]; exact hL⟩, pointer, by rw [pg]; exact heap, pointerBound⟩ (by omega)
      exact ⟨by omega, by omega, a3⟩
    | some x => dsimp only; exact ⟨by omega, by omega, c3⟩

#print axioms reqCheckAlloc_bounded
end InitECandidate.Runtime
