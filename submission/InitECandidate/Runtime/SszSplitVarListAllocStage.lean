import InitECandidate.Runtime.SszSplitVarListAfterAllocBody
import InitECandidate.Runtime.AllocationCall
import InitECandidate.Runtime.AllocationBodyBound
import InitECandidate.Runtime.AllocationFailureDeclaration
import InitECandidate.Runtime.AllocationFailureDeclarationNoReturn
import InitECandidate.Runtime.AllocationFailureDeclarationNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Facts of a returned split after the count check and allocation. -/
def SszSplitAllocReturned {σ : Type} (c : PanSemStateFiniteExact 64 σ) (lim count pointer : BitVec 64)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 σ) : Prop :=
  v = .rStruct [.val (.word pointer), .val (.word count)] ∧ ¬ lim < count ∧
    count * 16 ≤ (33806089496 : BitVec 64) - pointer ∧
    post.globals = (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word (allocationEnd pointer (count * 16)))) c).globals

theorem evaluate_sszSplitAllocStage {σ : Type} (c : PanSemStateFiniteExact 64 σ)
    (p len first count lim pointer : BitVec 64)
    (hp : c.locals.lookup (ofString "p") = some (.val (.word p)))
    (hlen : c.locals.lookup (ofString "len") = some (.val (.word len)))
    (hfirst : c.locals.lookup (ofString "first") = some (.val (.word first)))
    (hcount : c.locals.lookup (ofString "count") = some (.val (.word count)))
    (hlim : c.locals.lookup (ofString "lim") = some (.val (.word lim)))
    (code : c.code = originalRuntimeCode)
    (heap : c.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496)
    (small : count.toNat < 2 ^ 62) (enough : 2 * count.toNat + 2 ≤ c.clock) :
    let out := evaluateHOLFiniteState c (.seq sszSplitCountCheck sszSplitAlloc)
    c.clock ≤ out.2.clock + (2 * count.toNat + 2) ∧ out.2.clock ≤ c.clock ∧ out.1 ≠ none ∧
      out.1 ≠ some .timeOut ∧ (∀ v, out.1 = some (.returned v) → SszSplitAllocReturned c lim count pointer v out.2) := by
  have a1 : ofString "arr" ≠ ofString "p" := by decide_cbv
  have a2 : ofString "arr" ≠ ofString "len" := by decide_cbv
  have a3 : ofString "arr" ≠ ofString "first" := by decide_cbv
  have a4 : ofString "arr" ≠ ofString "count" := by decide_cbv
  rw [evaluateHOLFiniteState_seq_line780]
  unfold sszSplitCountCheck
  rw [evaluateHOLFiniteState_ite]
  by_cases bad : lim < count
  · have cond : @evalHOLExact 64 σ _ c.toExact (fun a => Classical.propDecidable (c.memaddrs a))
        (.cmp .lower (sszLocal "lim") (sszLocal "count")) = some (.val (.word 1#64)) := by
      simp [sszLocal, evalHOLExact, hlim, hcount, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, bad]
    rw [cond]
    dsimp only
    rw [if_neg (by decide : ¬ (1#64 : BitVec 64) = 0)]
    obtain ⟨x, run, abnormal, c1, c2⟩ := sszFail_abnormal c 22 code (by omega)
    rw [run]
    dsimp only
    exact ⟨by omega, c2, by rw [run]; simp, fun h => abnormal.2.1 (Option.some.inj (run.symm.trans h)),
      fun v h => absurd (Option.some.inj (run.symm.trans h)) (abnormal.2.2.2 v)⟩
  · have cond : @evalHOLExact 64 σ _ c.toExact (fun a => Classical.propDecidable (c.memaddrs a))
        (.cmp .lower (sszLocal "lim") (sszLocal "count")) = some (.val (.word 0#64)) := by
      simp [sszLocal, evalHOLExact, hlim, hcount, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, bad]
    rw [cond]
    dsimp only
    rw [if_pos (show (0#64 : BitVec 64) = 0 from rfl), evaluateHOLFiniteState_skip]
    dsimp only
    unfold sszSplitAlloc
    have args : evalListHOLFinite c (h := fun address => Classical.propDecidable (c.memaddrs address))
        [.panop .mul [sszLocal "count", .const 16]] = some [.val (.word (count * 16))] := by
      simp [sszLocal, evalListHOLFinite, evalListHOLExact, evalHOLExact, hcount, panOpHOL, valueIsWord, valueWord]
    by_cases request : count * 16 ≤ (33806089496 : BitVec 64) - pointer
    · obtain ⟨ready, _, rclock, _, rlocals, rcode, _, _, _, rglobals, decl⟩ :=
        evaluate_alloc_call_and_declaration c _ pointer (count * 16) args code (by omega) heap request
          (allocationEnd_within_heap pointer _ pointerBound request)
      rw [decl (ofString "arr") sszSplitAfterAlloc]
      dsimp only
      generalize hr : setVarHOLFinite (ofString "arr") (.val (.word pointer)) ready = r
      have up : ∀ k, k ≠ ofString "arr" → r.locals.lookup k = c.locals.lookup k := by
        intro k hk; rw [← hr]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk, rlocals]
      have rc : r.clock = c.clock - 1 := by rw [← hr]; exact rclock
      have rg : r.globals = ready.globals := by rw [← hr]; rfl
      have after := evaluate_sszSplitAfterAlloc r p len first count pointer ((up _ (Ne.symm a1)).trans hp)
        ((up _ (Ne.symm a2)).trans hlen) ((up _ (Ne.symm a3)).trans hfirst) ((up _ (Ne.symm a4)).trans hcount)
        (by rw [← hr]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        (by rw [← hr]; exact rcode.trans code) small (by omega)
      obtain ⟨t1, t2, ⟨q1, q2, q3⟩, t4⟩ := after
      refine ⟨by omega, by omega, q1, q2, fun v h => ⟨q3 v h, bad, request, ?_⟩⟩
      exact ((t4 v h).trans rg).trans rglobals
    · have over : ((33806089496 : BitVec 64) - pointer).toNat < (count * 16).toNat := by
        rw [BitVec.le_def] at request; omega
      have f1 := evaluate_alloc_request_failure_declaration c _ pointer (count * 16) (ofString "arr") .one
        sszSplitAfterAlloc args code heap over
      have f2 := evaluate_alloc_request_failure_declaration_no_timeout c _ pointer (count * 16) (ofString "arr") .one
        sszSplitAfterAlloc args code heap over (by omega)
      refine ⟨by omega, by omega, f1.1, f2, fun v h => absurd h ?_⟩
      exact evaluate_alloc_request_failure_declaration_no_return c _ pointer (count * 16) (ofString "arr") .one
        sszSplitAfterAlloc v args code heap over

#print axioms evaluate_sszSplitAllocStage
end InitECandidate.Runtime
