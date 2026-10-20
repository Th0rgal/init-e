import InitECandidate.Runtime.SourceCostLoopIf
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Call
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

section CallHelpers
/-! Flapjack helpers (no HOL declaration) for HOL's Call case: the `ALOOKUP`
over `ZIP` (`ALOOKUP_ALL_DISTINCT_EL`, `ALOOKUP_ZIP_FAIL`) and `FLOOKUP` over
`|++ ZIP` (`update_eq_zip_flookup`, `flookup_fupdate_zip_not_mem`) steps. -/

theorem loopCall_holAlookup_zip_not_memP {β : Type} :
    ∀ (xs : List Nat) (ys : List β) (n : Nat), n ∉ xs → holAlookup (xs.zip ys) n = none
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | x :: xs, y :: ys, n, h => by
      simp only [List.zip_cons_cons, holAlookup]
      rw [if_neg (fun e : x = n => h (e ▸ List.mem_cons_self))]
      exact loopCall_holAlookup_zip_not_memP xs ys n (fun hm => h (List.mem_cons_of_mem _ hm))

theorem loopCall_holAlookup_zip_getElem {β : Type} :
    ∀ (xs : List Nat) (ys : List β) (i : Nat) (_ : xs.Nodup) (hlen : xs.length = ys.length)
      (hi : i < xs.length),
      holAlookup (xs.zip ys) (xs[i]'hi) = some (ys[i]'(hlen ▸ hi))
  | [], _, _, _, _, hi => absurd hi (by simp)
  | _ :: _, [], _, _, hlen, _ => by simp at hlen
  | x :: xs, y :: ys, 0, _hd, _, _ => by simp [holAlookup]
  | x :: xs, y :: ys, i + 1, hd, hlen, hi => by
      simp only [List.zip_cons_cons, holAlookup, List.getElem_cons_succ]
      have hx : x ≠ xs[i]'(by simpa using hi) := by
        intro e; exact (List.nodup_cons.mp hd).1 (e ▸ List.getElem_mem _)
      rw [if_neg hx]
      exact loopCall_holAlookup_zip_getElem xs ys i (List.nodup_cons.mp hd).2 (by simpa using hlen) _

theorem loopCall_fupdateListHOL_zip_getElem {β : Type} (f : FiniteMap Nat β)
    (xs : List Nat) (ys : List β) (i : Nat) (hd : xs.Nodup) (hlen : xs.length = ys.length)
    (hi : i < xs.length) :
    FUPDATE_LIST_HOL f (xs.zip ys) (xs[i]'hi) = some (ys[i]'(hlen ▸ hi)) := by
  rw [FUPDATE_LIST_HOL_eq_FUPDATE_LIST]
  exact updateEqZipFlookupHOL xs ys f i hd hlen hi

theorem loopCall_fupdateListHOL_zip_not_mem {β : Type} (f : FiniteMap Nat β)
    (xs : List Nat) (ys : List β) (n : Nat) (hlen : xs.length = ys.length) (h : n ∉ xs) :
    FUPDATE_LIST_HOL f (xs.zip ys) n = f n := by
  have := FLOOKUP_FUPDATE_LIST_HOL_not_mem f (xs.zip ys) n (by
    rw [List.map_fst_zip (by omega)]; exact h)
  simpa [FLOOKUP] using this


/-- HOL's Call/Return `locals_rel` step (`crep_to_loopProofScript.sml:3490-3570`):
    writing the returned values into the return variables' slots after the call's
    `cut_res`, then cutting by `l`, preserves `locals_rel ctxt l`. -/
theorem loopCall_locals_rel_after_return {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact) (l : NumSet)
    (sl : HolFiniteMapExact Nat (HolWordLab width)) (S : Spt (WordLocW width))
    (rts rn : List Nat) (retvs : List (HolWordLab width))
    (h0 : crepToLoopLocalsRelExact ctxt l sl S)
    (hmap : rts.mapM ctxt.vars.lookup = some rn) (hrnl : ∀ n ∈ rn, sptMem n l)
    (hrts : rts.Nodup) (hrn : rn.Nodup) (hlen : retvs.length = rts.length) :
    crepToLoopLocalsRelExact ctxt l (sl.updateListEq (rts.zip retvs))
      (sptInter (LoopSemStateFiniteExact.sptAlistInsert rn (retvs.map wlabWlocExact)
        (sptInter S l)) l) := by
  have hrnlen : rts.length = rn.length := opt_mmap_length_eq rts _ rn hmap
  refine ⟨h0.1, h0.2.1, fun k hk => ?_, fun vn val hval => ?_⟩
  · have hk' : (sptLookup k l).isSome := hk
    show (sptLookup k (sptInter _ l)).isSome
    rw [sptLookup_sptInter, if_pos hk', lookup_alist_insert_any]
    split
    · rw [sptLookup_sptInter, if_pos hk']; exact h0.2.2.1 k hk
    · rfl
  · simp only [HolFiniteMapExact.lookup_updateListEq] at hval
    by_cases hmem : vn ∈ rts
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
      rw [loopCall_fupdateListHOL_zip_getElem _ rts retvs i hrts hlen.symm hi] at hval
      have hvar := opt_mmap_el rts ctxt.vars.lookup rn i hmap hi
      have hi' : i < rn.length := hrnlen ▸ hi
      have hnl : sptMem (rn[i]'hi') l := hrnl _ (List.getElem_mem _)
      refine ⟨rn[i]'hi', hvar, hnl, ?_⟩
      have hnl' : (sptLookup (rn[i]'hi') l).isSome := hnl
      rw [sptLookup_sptInter, if_pos hnl', lookup_alist_insert_any,
        loopCall_holAlookup_zip_getElem rn _ i hrn (by simp [hlen, hrnlen]) hi']
      simp only [List.getElem_map, ← Option.some.inj hval]
      cases retvs[i] <;> rfl
    · rw [loopCall_fupdateListHOL_zip_not_mem _ rts retvs vn hlen.symm hmem] at hval
      obtain ⟨n, hn1, hn2, hn3⟩ := h0.2.2.2 vn val hval
      have hnrn : n ∉ rn := by
        intro hm
        obtain ⟨j, hj, hjn⟩ := List.getElem_of_mem hm
        have hj' : j < rts.length := hrnlen ▸ hj
        have hvar := opt_mmap_el rts ctxt.vars.lookup rn j hmap hj'
        have := h0.1 vn _ n _ hn1 hvar hjn.symm
        exact hmem (this ▸ List.getElem_mem _)
      have hnl' : (sptLookup n l).isSome := hn2
      refine ⟨n, hn1, hn2, ?_⟩
      rw [sptLookup_sptInter, if_pos hnl', lookup_alist_insert_any,
        loopCall_holAlookup_zip_not_memP rn _ n hnrn]
      simp only
      rw [sptLookup_sptInter, if_pos hnl']
      exact hn3

theorem loopCall_locals_rel_inter {width : Nat} [NeZero width] (ctxt : CrepToLoopContextExact) (l : NumSet)
    (sl : HolFiniteMapExact Nat (HolWordLab width)) (tl : Spt (WordLocW width))
    (h : crepToLoopLocalsRelExact ctxt l sl tl) :
    crepToLoopLocalsRelExact ctxt l sl (sptInter tl l) := by
  refine ⟨h.1, h.2.1, fun k hk => ?_, fun vn val hval => ?_⟩
  · have hk' : (sptLookup k l).isSome := hk
    show (sptLookup k (sptInter tl l)).isSome
    rw [sptLookup_sptInter, if_pos hk']
    exact h.2.2.1 k hk
  · obtain ⟨n, hn1, hn2, hn3⟩ := h.2.2.2 vn val hval
    have hnl : (sptLookup n l).isSome := hn2
    refine ⟨n, hn1, hn2, ?_⟩
    show sptLookup n (sptInter tl l) = _
    rw [sptLookup_sptInter, if_pos hnl]
    exact hn3

end CallHelpers

/-- Named obligation (to be discharged by the loop_call/loop_live work
transfer, never assumed in a final theorem): optimisation does not increase the
executed Loop work of a function-exit run. -/
def LoopOptimiseWork : Prop :=
  ∀ (F : Type) (q : HolLoopProg 64) (s : LoopSemStateFiniteExact 64 F)
    (r : LoopSemStateFiniteExact.LoopResultExact 64) (post : LoopSemStateFiniteExact 64 F) (w : Nat),
    LoopWork s q (some r, post) w → r ≠ .error → (∀ n, r ≠ .break n) → (∀ n, r ≠ .continue n) →
    ∃ w', LoopWork s (optimiseHOL q) (some r, post) w' ∧ w' ≤ w

theorem crepListWork_ge_length : ∀ es : List (CrepExpHOL 64), es.length ≤ crepListWork es
  | [] => by simp [crepListWork]
  | e :: es => by
    have h := crepListWork_ge_length es
    have : 1 ≤ crepNodeWork e := by cases e <;> simp [crepNodeWork] <;> omega
    simp only [crepListWork, List.length_cons]; omega

#print axioms crepListWork_ge_length
end InitECandidate.Runtime.FineCost
