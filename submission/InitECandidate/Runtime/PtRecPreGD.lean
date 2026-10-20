import InitECandidate.Runtime.PtRegTRGD
import InitECandidate.Runtime.PreStateAccountArena
import InitECandidate.Runtime.GetCodeGD
/-!
The actual `record_pre_state_read(addr)` over the registry with owned region (`RegTR`): `htab_set` on the block
pre-state read table (registry index `kB`, cell `bs + 72`) re-establishes the registry at the exit heap with its region
grown by the fresh heap; memory below the entry heap changes only inside the registry region.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Exit of a registry-table set. -/
def RPPost (n : Nat) (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (D : BitVec 64 → Prop) (B : Bool)
    (ko : Fin n) (Rr : BitVec 64 → Prop) (H0 Nj : BitVec 64) (M0 : Mem) (M' : Mem) (G' : GA) : Prop :=
  ∃ H' : BitVec 64, HeapIs G' H' ∧ H0.toNat ≤ H'.toNat ∧
    RegTR n c T Out H' M' D B ko (fun x => Rr x ∨ (H0.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) ∧
    G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∀ x, x.toNat < H0.toNat → ¬ Rr x → M' x = M0 x

section rp
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kB : Fin n} {Rr : BitVec 64 → Prop}
  {Bs J C SKB Nj H0 : BitVec 64} {M0 : Mem}

theorem recordPreR_aqgd (ne : kB ≠ ko) (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcB : c kB = Bs + 72#64) (p0 : P0.toNat ≤ H0.toNat) (hwP : w.toNat < P0.toNat) (hwR : ¬ Rr w) :
    AQGD D B (JWS SP0 P0 FM G0 J C SKB) w (fun _ => False)
      (fun L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
        RegTR n c T Out H0 M D B ko Rr ∧ M = M0 ∧ HeapIs G H0 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (fun _ _ _ => True) (fun _ M' G' => RPPost n c T Out D B ko Rr H0 Nj M0 M' G')
      (sourceFunctionBody Guest.guestFn_record_pre_state_read) := by
  rw [source_recordPreRead_body]
  refine aqgd_seq (Q := fun _ M G => RPPost n c T Out D B ko Rr H0 Nj M0 M G) ?_
    (aqgd_return _ (fun _ _ _ _ _ pre _ _ => pre))
  refine aqgd_conseq (P := fun L M G => ∃ q : (Fin n → TLay) × BitVec 64,
      (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ HeapIs G H0 ∧
      RegPure n c T Out H0 q.1 ∧ RegMem n c T q.1 M ∧ TCont D B M (T ko) (q.1 ko) ∧
      (∀ x, (q.1 ko).arr x → x.toNat < H0.toNat) ∧ (∀ i x, (x = c i ∨ HdrR (T i) x ∨ (q.1 i).arr x) → Rr x) ∧
      M = M0 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (aqgd_ex (fun q => ?_)) (fun L M G ⟨hl,⟨l,pure,mem,tc,ab,rr⟩,hM,hH,hn⟩ =>
      ⟨(l,H0),hl,hH,pure,mem,tc,ab,rr,hM,hn⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  rcases q with ⟨l,Hq⟩
  dsimp only
  refine aqgd_callSpec (Vn' := fun _ => True)
    (Pe := fun _ M0' G0' L M G => (∃ A : BitVec 64, LK (irP0 (T kB) A 1#64) L) ∧ M = M0' ∧ G = G0')
    (RRe := fun _ M0' G0' _ M' G' => G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      ∃ H' : BitVec 64, HeapIs G' H' ∧ SetPost (T kB) ((l kB).canon (T kB) H0) M0' (l kB).C (l kB).SD
        (l kB).KS (l kB).VS (l kB).US (l kB).OS (l kB).OPS H0 M' H')
    _ _ _ _ _ originalRuntimeCode_hashSet_lookup (by simp) ?_ ?_ ?_
  · intro L0 M0' G0' ⟨_,hH,pure,mem,_,_,rr,_,hn⟩
    have lay := (pure.1 kB).1
    have hwk : ¬ (l kB).canon (T kB) H0 w := fun hc => by
      rcases hc with h | h | h
      · exact hwR (rr kB w (Or.inr (Or.inl h)))
      · exact hwR (rr kB w (Or.inr (Or.inr h)))
      · omega
    refine aqgd_conseq (P := fun L M G => ∃ A : BitVec 64, LK (irP0 (T kB) A 1#64) L ∧ M = M0' ∧ G = G0') ?_
      (fun _ _ _ ⟨⟨A,lk⟩,hm,hg⟩ => ⟨A,lk,hm,hg⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
    refine aqgd_exE (fun A => ?_)
    refine aqgd_conseq (aqgd_jws (aqgd_of_aqg (aqg_of_aqmh_j (J := J) (C := C) (N := Nj)
      originalRuntimeCode_hashSet_lookup (by decide_cbv) (by decide_cbv) (by decide_cbv)
      (aqmh_rebound (set_aqmh (P0 := H0) (T kB) A 1#64 _ (l kB).KL (l kB).SD (l kB).C (l kB).N (l kB).KS
        (l kB).VS (l kB).US (l kB).OS (l kB).OPS (l kB).b lay M0' hwk H0 (le_refl _)) p0)))
      (keepsSkBuf_of_installed originalRuntimeCode_hashSet_lookup (by decide))) ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M G ⟨hl,hM,hG⟩
      subst hM hG
      exact ⟨hn,H0,hH,le_refl _,hl,(mem kB).2,rfl,rfl⟩
    · intro v M' G' ⟨hn',H',hH',post⟩
      exact ⟨hn',H',hH',post⟩
  · intro F s values callee rs aw G hG ⟨⟨A,hA⟩,_,_,mem,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨eg,_⟩ := aw.1.1.2.2.2 (ofString "bs") (by decide)
    have cB := (mem kB).1
    rw [hcB] at cB
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,eg,hBs,hA,wordOpHOL,wordOp,valueIsWord,valueWord,memLoadHOLExact,cB]
      at args
    by_cases hd : s.memaddrs (Bs + 72#64)
    swap
    · simp [hd] at args
    simp only [hd,if_true,Option.some.injEq] at args
    subst args
    rw [pan_three_word_lookup _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
      originalRuntimeCode_hashSet_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    refine ⟨⟨A,fun p hp => ?_⟩,rfl,rfl⟩
    simp only [irP0,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  · intro L M G v M' G' ⟨_,hH,pure,mem,tc,ab,rr,hM,_⟩ ⟨hn',H',hH',post⟩
    subst hM
    obtain ⟨reg',le,frX⟩ := regTR_set ne l pure mem tc ab rr post
    exact ⟨H',hH',le,reg',hn',frX⟩

#print axioms recordPreR_aqgd
end rp
end InitECandidate.Runtime
