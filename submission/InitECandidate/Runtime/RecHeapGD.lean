import InitECandidate.Runtime.RecBeStoreGD
/-!
Heap control over the pinned-journal arena with exact globals effects: `alloc` and `heap_release` change only the heap
pointer (`OnlyHeap`), so `secp_accel_scratch` (`ScrIs`) is kept; `aqgd_addRet` adds a returned-outcome globals relation.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Only the heap pointer may differ. -/
def OnlyHeap (g g' : GA) : Prop := ∀ n, n ≠ ofString "heap_ptr" → g'.lookup n = g.lookup n

theorem scrIs_onlyHeap {Sc : BitVec 64} {g g' : GA} (h : OnlyHeap g g') (s : ScrIs Sc g) : ScrIs Sc g' := by
  unfold ScrIs; rw [h _ (by decide)]; exact s

section ar
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- Add a returned-outcome globals relation to a spec. -/
theorem aqgd_addRet {R : GA → GA → Prop} {P Q : GA → Mem → GA → Prop} {body : ProgHOL 64}
    (hr : ReturnedRel R body) (h : AQGD D B A w Vn P Q RR body) (G0 : GA) :
    AQGD D B A w Vn (fun L M G => P L M G ∧ G = G0) Q (fun v M G => RR v M G ∧ R G0 G) body := by
  intro F s code dom aw sl H hH ⟨pre,hg⟩
  obtain ⟨m,a,n,r,c,b⟩ := h F s code dom aw sl H hH pre
  refine ⟨m,a,n,fun v e => ?_,c,b⟩
  obtain ⟨H',hH',rr⟩ := r v e
  refine ⟨H',hH',rr,?_⟩
  unfold GIs at hH hH'
  subst hH hH' hg
  unfold ReturnedRel at hr
  exact hr s _ v code (Prod.ext e rfl)

#print axioms aqgd_addRet
end ar

section al
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}

/-- `alloc(n)` over the pinned-journal arena: returns the heap pointer `H`, raises it by at least `n` within the
cap, and changes no other global. -/
theorem allocN_spec (Nn H : BitVec 64) (M0 : Mem) (Gk : GA) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => True)
      (fun L M G => (L.lookup (ofString "n") = some (.val (.word Nn)) ∧ M = M0 ∧ HeapIs G H) ∧ G = Gk)
      (fun _ _ _ => True)
      (fun v M' G' => (v = .val (.word H) ∧ M' = M0 ∧ ∃ H' : BitVec 64, HeapIs G' H' ∧
        H.toNat + Nn.toNat ≤ H'.toNat ∧ H'.toNat ≤ 33806089496) ∧ OnlyHeap Gk G')
      (sourceFunctionBody Guest.guestFn_alloc) := by
  have hr : ReturnedRel (fun g g' => OnlyHeap g g') (sourceFunctionBody Guest.guestFn_alloc) := by
    have := alloc_returnedRel
    unfold ReturnedRel at this ⊢
    intro F s p v code e; exact (this s p v code e).1
  refine aqgd_conseq (aqgd_addRet hr ?_ Gk) (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h)
  refine aqgd_jwsn (keepsJournalN_of_installed originalRuntimeCode_allocation_lookup (by decide)) ?_
  refine aqgd_conseq (aqgd_jws (aqgd_of_aqg (aqg_of_aqmh_j (J := J) (C := C) (N := Nj)
    originalRuntimeCode_allocation_lookup (by decide_cbv) (by decide_cbv) (by decide_cbv)
    (alloc_aqmh (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (w := w) Nn H M0)))
    (keepsSkBuf_of_installed originalRuntimeCode_allocation_lookup (by decide))) ?_ (fun _ _ _ _ => trivial) ?_
  · intro L M G ⟨⟨hl,hM,hH⟩,hn⟩
    exact ⟨hn,H,hH,hl,hM,rfl⟩
  · intro v M' G' ⟨_,H',hH',hM,ev,_,_,c1,c2,_⟩
    exact ⟨ev,hM,H',hH',c1,c2⟩

#print axioms allocN_spec

/-- `heap_release(m)` over the pinned-journal arena: sets the heap pointer to `Mk`, nothing else. -/
theorem heapReleaseN_spec (M0 : Mem) (Mk : BitVec 64) (lo : P0.toNat ≤ Mk.toNat) (hi : Mk.toNat ≤ 33806089496)
    (al : Mk.toNat % 8 = 0) (Gk : GA) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False)
      (fun L M G => (L.lookup (ofString "m") = some (.val (.word Mk)) ∧ M = M0) ∧ G = Gk) (fun _ _ _ => True)
      (fun _ M G => (M = M0 ∧ HeapIs G Mk) ∧ OnlyHeap Gk G) (sourceFunctionBody Guest.guestFn_heap_release) := by
  rw [source_heapRelease_body]
  refine aqgd_seq (Q := fun _ M G => (M = M0 ∧ HeapIs G Mk) ∧ OnlyHeap Gk G)
    (aqgd_assignGlobal _ _ (fun s v aw ⟨⟨hm,hM⟩,hg⟩ _ ev => ?_))
    (aqgd_return _ (fun _ _ _ _ hG pre _ _ => by unfold GIs at hG; subst hG; exact pre))
  simp [EV,evalHOLExact,hm] at ev; subst ev
  have e : (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word Mk)) s).globals =
      s.globals.update (ofString "heap_ptr",.val (.word Mk)) := by simp [setGlobalHOLFinite]
  rw [e]
  subst hg
  exact ⟨⟨jws_setHeap aw.1 Mk lo hi al,by rw [lookup_update_ne' _ _ (by decide)]; exact aw.2⟩,
    ⟨hM,lookup_update_eq' _ _ _⟩,fun n hn => lookup_update_ne' _ _ hn⟩

#print axioms heapReleaseN_spec
end al
end InitECandidate.Runtime
