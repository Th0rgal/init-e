import InitECandidate.Runtime.SszSplitVarListSlicesAfterAlloc
import InitECandidate.Runtime.SszSplitVarListFirstStage
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_sszSplitAllocStageB {σ : Type} (c : PanSemStateFiniteExact 64 σ)
    (p len first count lim pointer : BitVec 64)
    (hp : c.locals.lookup (ofString "p") = some (.val (.word p)))
    (hlen : c.locals.lookup (ofString "len") = some (.val (.word len)))
    (hfirst : c.locals.lookup (ofString "first") = some (.val (.word first)))
    (hcount : c.locals.lookup (ofString "count") = some (.val (.word count)))
    (hlim : c.locals.lookup (ofString "lim") = some (.val (.word lim)))
    (code : c.code = originalRuntimeCode)
    (heap : c.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496) (nz : count ≠ 0)
    (small : count.toNat < 2 ^ 60) (enough : 2 * count.toNat + 2 ≤ c.clock) :
    ∀ v, (evaluateHOLFiniteState c (.seq sszSplitCountCheck sszSplitAlloc)).1 = some (.returned v) →
      SszSplitSlices c.memory c.memaddrs p len first pointer count
        (evaluateHOLFiniteState c (.seq sszSplitCountCheck sszSplitAlloc)).2.memory := by
  have a1 : ofString "arr" ≠ ofString "p" := by decide_cbv
  have a2 : ofString "arr" ≠ ofString "len" := by decide_cbv
  have a3 : ofString "arr" ≠ ofString "first" := by decide_cbv
  have a4 : ofString "arr" ≠ ofString "count" := by decide_cbv
  intro v returned
  rw [evaluateHOLFiniteState_seq_line780] at returned ⊢
  unfold sszSplitCountCheck at returned ⊢
  rw [evaluateHOLFiniteState_ite] at returned ⊢
  by_cases bad : lim < count
  · have cond : @evalHOLExact 64 σ _ c.toExact (fun a => Classical.propDecidable (c.memaddrs a))
        (.cmp .lower (sszLocal "lim") (sszLocal "count")) = some (.val (.word 1#64)) := by
      simp [sszLocal, evalHOLExact, hlim, hcount, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, bad]
    rw [cond] at returned
    dsimp only at returned
    rw [if_neg (by decide : ¬ (1#64 : BitVec 64) = 0)] at returned
    obtain ⟨x, run, abnormal, _, _⟩ := sszFail_abnormal c 22 code (by omega)
    rw [run] at returned
    dsimp only at returned
    exact absurd (Option.some.inj (run.symm.trans returned)) (abnormal.2.2.2 v)
  · have cond : @evalHOLExact 64 σ _ c.toExact (fun a => Classical.propDecidable (c.memaddrs a))
        (.cmp .lower (sszLocal "lim") (sszLocal "count")) = some (.val (.word 0#64)) := by
      simp [sszLocal, evalHOLExact, hlim, hcount, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, bad]
    rw [cond] at returned ⊢
    dsimp only at returned ⊢
    rw [if_pos (show (0#64 : BitVec 64) = 0 from rfl), evaluateHOLFiniteState_skip] at returned ⊢
    dsimp only at returned ⊢
    unfold sszSplitAlloc at returned ⊢
    have args : evalListHOLFinite c (h := fun address => Classical.propDecidable (c.memaddrs address))
        [.panop .mul [sszLocal "count", .const 16]] = some [.val (.word (count * 16))] := by
      simp [sszLocal, evalListHOLFinite, evalListHOLExact, evalHOLExact, hcount, panOpHOL, valueIsWord, valueWord]
    by_cases request : count * 16 ≤ (33806089496 : BitVec 64) - pointer
    · obtain ⟨ready, _, rclock, rmem, rlocals, rcode, rdom, _, _, _, decl⟩ :=
        evaluate_alloc_call_and_declaration c _ pointer (count * 16) args code (by omega) heap request
          (allocationEnd_within_heap pointer _ pointerBound request)
      rw [decl (ofString "arr") sszSplitAfterAlloc] at returned ⊢
      dsimp only at returned ⊢
      generalize hr : setVarHOLFinite (ofString "arr") (.val (.word pointer)) ready = r at returned ⊢
      have up : ∀ k, k ≠ ofString "arr" → r.locals.lookup k = c.locals.lookup k := by
        intro k hk; rw [← hr]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk, rlocals]
      have rc : r.clock = c.clock - 1 := by rw [← hr]; exact rclock
      have rm : r.memory = c.memory := by rw [← hr]; exact rmem
      have rd : r.memaddrs = c.memaddrs := by rw [← hr]; exact rdom
      have slices := evaluate_sszSplitAfterAllocB r p len first count pointer ((up _ (Ne.symm a1)).trans hp)
        ((up _ (Ne.symm a2)).trans hlen) ((up _ (Ne.symm a3)).trans hfirst) ((up _ (Ne.symm a4)).trans hcount)
        (by rw [← hr]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        (by rw [← hr]; exact rcode.trans code) nz small (by omega) v returned
      rw [rm, rd] at slices
      exact slices
    · have over : ((33806089496 : BitVec 64) - pointer).toNat < (count * 16).toNat := by
        rw [BitVec.le_def] at request; omega
      exact absurd returned (evaluate_alloc_request_failure_declaration_no_return c _ pointer (count * 16)
        (ofString "arr") .one sszSplitAfterAlloc v args code heap over)

#print axioms evaluate_sszSplitAllocStageB
end InitECandidate.Runtime
