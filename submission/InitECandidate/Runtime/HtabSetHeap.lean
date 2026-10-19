import InitECandidate.Runtime.HtabGrowHeap
import InitECandidate.Runtime.HtabSetLayArena
/-!
Heap-aware `htab_set`.  The table is described against its canonical footprint at the current heap pointer
(header, its own five arrays, and the heap above the pointer), so two tables whose headers and arrays are disjoint
stay separated across calls: a set on one table only writes inside its entry footprint, and any arrays it allocates
lie between the entry and exit heap pointers.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {SP0 P0 FM w : BitVec 64} {G0 : HolFiniteMapExact MlS (ValueHOL 64)}

/-- Canonical footprint of a table at heap pointer `H`: its header, its five arrays, and the heap from `H`. -/
def Canon (T C SD KS VS US OS OPS H : BitVec 64) (x : BitVec 64) : Prop :=
  (T.toNat ≤ x.toNat ∧ x.toNat < T.toNat + 72) ∨ ArrOf C SD KS VS US OS OPS x ∨ H.toNat ≤ x.toNat

/-- Any valid layout is valid against its canonical footprint at any heap pointer above its bound. -/
theorem hlay_canon {P T : BitVec 64} {E : BitVec 64 → Prop} {KL SD C N KS VS US OS OPS : BitVec 64} {b : Nat}
    (lay : HLay P T E KL SD C N KS VS US OS OPS b) {H : BitVec 64} (le : P.toNat ≤ H.toNat) :
    HLay H T (Canon T C SD KS VS US OS OPS H) KL SD C N KS VS US OS OPS b :=
  ⟨lay.pow,lay.fits,lay.sdAl,lay.ksAl,lay.usAl,lay.cnt,fun x lo hi => Or.inl ⟨lo,hi⟩,
    by have := lay.hdrP; omega,lay.eEnd,fun x hx => Or.inr (Or.inr hx),
    ⟨lay.keysR.1,lay.keysR.2.1,fun x lo hi => Or.inr (Or.inl (Or.inl ⟨lo,hi⟩))⟩,
    ⟨lay.valsR.1,lay.valsR.2.1,fun x lo hi => Or.inr (Or.inl (Or.inr (Or.inl ⟨lo,hi⟩)))⟩,
    ⟨lay.usedR.1,lay.usedR.2.1,fun x lo hi => Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨lo,hi⟩))))⟩,
    ⟨lay.orderR.1,lay.orderR.2.1,fun x lo hi => Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨lo,hi⟩)))))⟩,
    ⟨lay.oposR.1,lay.oposR.2.1,fun x lo hi => Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨lo,hi⟩)))))⟩⟩

/-- The arrays of a valid layout lie in its footprint. -/
theorem arrOf_foot {P T : BitVec 64} {E : BitVec 64 → Prop} {KL SD C N KS VS US OS OPS : BitVec 64} {b : Nat}
    (lay : HLay P T E KL SD C N KS VS US OS OPS b) (x : BitVec 64) (h : ArrOf C SD KS VS US OS OPS x) : E x := by
  rcases h with ⟨lo,hi⟩ | ⟨lo,hi⟩ | ⟨lo,hi⟩ | ⟨lo,hi⟩ | ⟨lo,hi⟩
  · exact lay.keysR.2.2 x lo hi
  · exact lay.valsR.2.2 x lo hi
  · exact lay.usedR.2.2 x lo hi
  · exact lay.orderR.2.2 x lo hi
  · exact lay.oposR.2.2 x lo hi

/-- Post-state of a heap-aware `htab_set` started at heap pointer `Hc` on a table with footprint `E` and arrays
`C SD KS VS US OS OPS`: the exit heap pointer `H` is at least `Hc`, memory is unchanged outside `E`, and some
valid layout (against its canonical footprint at `H`) is in memory whose arrays are the old arrays or lie in
`[Hc, H)`. -/
def SetPost (T : BitVec 64) (E : BitVec 64 → Prop) (M0 : Mem) (C SD KS VS US OS OPS Hc : BitVec 64) (M : Mem)
    (H : BitVec 64) : Prop :=
  Hc.toNat ≤ H.toNat ∧ (∀ x, ¬ E x → M x = M0 x) ∧
    ∃ (KL' SD' C' N' KS' VS' US' OS' OPS' : BitVec 64) (b' : Nat),
      HLay H T (Canon T C' SD' KS' VS' US' OS' OPS' H) KL' SD' C' N' KS' VS' US' OS' OPS' b' ∧
      Hdr M T KL' SD' C' N' KS' VS' US' OS' OPS' ∧
      LayIn (fun x => ArrOf C SD KS VS US OS OPS x ∨ (Hc.toNat ≤ x.toNat ∧ x.toNat < H.toNat))
        C' SD' KS' VS' US' OS' OPS'

/-- Before the insertion: a valid layout with room for one more entry, as in `SetPost`. -/
def SetMid (T : BitVec 64) (E : BitVec 64 → Prop) (M0 : Mem) (C SD KS VS US OS OPS Hc : BitVec 64) (M : Mem)
    (H : BitVec 64) : Prop :=
  Hc.toNat ≤ H.toNat ∧ (∀ x, ¬ E x → M x = M0 x) ∧
    ∃ (KL' SD' C' N' KS' VS' US' OS' OPS' : BitVec 64) (b' : Nat),
      HLay H T (Canon T C' SD' KS' VS' US' OS' OPS' H) KL' SD' C' N' KS' VS' US' OS' OPS' b' ∧
      Hdr M T KL' SD' C' N' KS' VS' US' OS' OPS' ∧ N'.toNat + 1 < C'.toNat ∧
      LayIn (fun x => ArrOf C SD KS VS US OS OPS x ∨ (Hc.toNat ≤ x.toNat ∧ x.toNat < H.toNat))
        C' SD' KS' VS' US' OS' OPS'

theorem aqm_pure {Vn : MlS → Prop} {φ : Prop} {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → Prop}
    {RR : ValueHOL 64 → Mem → Prop} {p : ProgHOL 64} (h : φ → AQM SP0 P0 FM G0 w Vn P Q RR p) :
    AQM SP0 P0 FM G0 w Vn (fun L M => φ ∧ P L M) (fun L M => φ ∧ Q L M) (fun v M => φ ∧ RR v M) p := by
  intro F s code dom aw sl ⟨f,pre⟩
  obtain ⟨m,a,n,r,c,b⟩ := h f F s code dom aw sl pre
  exact ⟨m,a,fun e => ⟨(n e).1,f,(n e).2⟩,fun v e => ⟨f,r v e⟩,c,b⟩


/-- The canonical footprint of a mid-set layout lies inside the entry footprint. -/
theorem canon_sub {P T : BitVec 64} {E : BitVec 64 → Prop} {KL SD C N KS VS US OS OPS : BitVec 64} {b : Nat}
    (lay : HLay P T E KL SD C N KS VS US OS OPS b) {Hc H C' SD' KS' VS' US' OS' OPS' : BitVec 64}
    (p0 : P.toNat ≤ Hc.toNat) (hle : Hc.toNat ≤ H.toNat)
    (inn : LayIn (fun x => ArrOf C SD KS VS US OS OPS x ∨ (Hc.toNat ≤ x.toNat ∧ x.toNat < H.toNat))
      C' SD' KS' VS' US' OS' OPS') :
    ∀ x, Canon T C' SD' KS' VS' US' OS' OPS' H x → E x := by
  rintro x (⟨lo,hi⟩ | h | h)
  · exact lay.hdr x lo hi
  · rcases inn x h with h' | ⟨lo,_⟩
    · exact arrOf_foot lay x h'
    · exact lay.fresh x (by omega)
  · exact lay.fresh x (by omega)

set_option maxHeartbeats 8000000 in
/-- Heap-aware `htab_set` from heap pointer `Hc` (at least `P0`): every word outside the footprint is kept in every
outcome, and a return satisfies `SetPost`: memory unchanged outside `E`, and a valid layout in memory against its
canonical footprint at the exit heap pointer, whose arrays are the old ones or fresh ones in `[Hc, exit)`. -/
theorem set_aqmh (T Kk V : BitVec 64) (E : BitVec 64 → Prop) (KL SD C N KS VS US OS OPS : BitVec 64) (b : Nat)
    (lay : HLay P0 T E KL SD C N KS VS US OS OPS b) (M0 : Mem) (hw : ¬ Foot P0 T E w) (Hc : BitVec 64)
    (p0 : P0.toNat ≤ Hc.toNat) :
    AQMH SP0 P0 FM G0 w (fun _ => True)
      (fun L M H => LK (irP0 T Kk V) L ∧ Hdr M T KL SD C N KS VS US OS OPS ∧ M = M0 ∧ H = Hc)
      (fun _ _ _ => True) (fun _ M' H' => SetPost T E M0 C SD KS VS US OS OPS Hc M' H')
      (sourceFunctionBody Guest.guestFn_htab_set) := by
  have fitT : T.toNat + 72 < 2 ^ 64 := by have := lay.eEnd; omega
  have cHE : C.toNat ≤ 33806089496 := by have := arr_end lay.usedR lay.eEnd; omega
  have nC := lay.cnt
  have hwP : w.toNat < P0.toNat := by by_contra h; exact hw (lay.fresh w (by omega))
  have postOld : ∀ (M : Mem) (H : BitVec 64), Hc.toNat ≤ H.toNat → MI P0 T E M0 KL SD C N KS VS US OS OPS M →
      SetPost T E M0 C SD KS VS US OS OPS Hc M H := fun M H hle hm =>
    ⟨hle,hm.2,KL,SD,C,N,KS,VS,US,OS,OPS,b,hlay_canon lay (by omega),hm.1,fun x hx => Or.inl hx⟩
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_htab_set,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,List.map_cons,List.map_nil,Option.map_none]
  refine aqmh_conseq (P := fun L M H => LK (irP0 T Kk V) L ∧ MI P0 T E M0 KL SD C N KS VS US OS OPS M ∧ H = Hc) ?_
    (fun L M H h => ⟨h.1,⟨h.2.1,fun x _ => by rw [h.2.2.1]⟩,h.2.2.2⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  -- i = htab_find_slot(t, key)
  refine aqmh_decCallSpec (Vn' := fun _ => False)
    (Pe := fun _ M0' H0 L M H => (L.lookup (ofString "t") = some (.val (.word T)) ∧ M = M0' ∧
      M (T + 16) = .word C) ∧ H = H0)
    (RRe := fun _ M0' H0 v M' H' => H0.toNat ≤ H'.toNat ∧ M' = M0' ∧ ∃ i : BitVec 64, v = .val (.word i) ∧
      i.toNat ≤ C.toNat)
    (Pc := fun L M H => Hc.toNat ≤ H.toNat ∧ ∃ I : BitVec 64, LK ((ofString "i",I) :: irP0 T Kk V) L ∧
      I.toNat ≤ C.toNat ∧ MI P0 T E M0 KL SD C N KS VS US OS OPS M)
    (Qc := fun _ _ _ => True) _ _ _ _ _ _ _ originalRuntimeCode_hashFind_lookup (by simp)
    (fun _ M0' H0 _ => aqmh_conseq (aqmh_of_aqm (P := fun H L M => H = H0 ∧ _) (Q := fun H L M => H = H0 ∧ True)
      (RR := fun H v M => H = H0 ∧ _) (fun H _ => aqm_bound_eq (findSlot_aqm T C b lay.pow M0')))
      (fun L M H ⟨h1,h2⟩ => ⟨h2,h1⟩) (fun _ _ _ _ => trivial)
      (fun v M H' ⟨H,_,hle,e,r⟩ => by subst e; exact ⟨hle,r⟩)) ?_ (fun _ => rfl) ?_ ?_
    (fun _ _ _ _ _ _ _ _ => trivial)
  · intro F s values callee rs _ H _ ⟨hl,hm,hh⟩ _ args lookup
    have ht := lk_get hl (ofString "t") T (by simp [irP0])
    have hk := lk_get hl (ofString "key") Kk (by simp [irP0])
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,ht,hk] at args
    subst args
    rw [pan_two_word_lookup _ _ _ _ _ _ _ (by decide) originalRuntimeCode_hashFind_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],rfl,hm.1.2.2.1⟩,rfl⟩
  · intro L M H v M' H' ⟨hl,hm,hh⟩ ⟨hle,eM,I,ev,hI⟩ _
    subst eM ev hh
    exact ⟨hle,I,lk_cons hl _ _ (by unfold irP0; lkne),hI,hm⟩
  -- found: update the value slot and return (no allocation)
  refine aqmh_seq (Q := fun L M H => Hc.toNat ≤ H.toNat ∧ ∃ I : BitVec 64, LK ((ofString "i",I) :: irP0 T Kk V) L ∧
      I.toNat ≤ C.toNat ∧ MI P0 T E M0 KL SD C N KS VS US OS OPS M) (aqmh_conseq (aqmh_of_aqm
      (P := fun H L M => Hc.toNat ≤ H.toNat ∧ ∃ I : BitVec 64, LK ((ofString "i",I) :: irP0 T Kk V) L ∧
        I.toNat ≤ C.toNat ∧ MI P0 T E M0 KL SD C N KS VS US OS OPS M)
      (Q := fun H L M => Hc.toNat ≤ H.toNat ∧ ∃ I : BitVec 64, LK ((ofString "i",I) :: irP0 T Kk V) L ∧
        I.toNat ≤ C.toNat ∧ MI P0 T E M0 KL SD C N KS VS US OS OPS M)
      (RR := fun H _ M => Hc.toNat ≤ H.toNat ∧ MI P0 T E M0 KL SD C N KS VS US OS OPS M)
      (fun H _ => aqm_pure (fun _ => ?_)))
      (fun _ _ _ h => h) (fun L M H' ⟨H,_,hle,h1,h2⟩ => ⟨by omega,h2⟩)
      (fun v M H' ⟨H,_,hle,h1,h2⟩ => postOld M H' (by omega) h2)) ?_
  · refine aqm_ite (CT := fun L M => ∃ I : BitVec 64,
      L.lookup (ofString "i") = some (.val (.word I)) ∧ I ≠ C) (CF := fun _ _ => True) _ ?_ ?_
      (aqm_conseq aqm_skip (fun _ _ h => h.1) (fun _ _ h => h) (fun _ _ h => h))
    · intro F s x _ ⟨I,hl,_,hm⟩ _ ev
      refine ⟨fun nz => ⟨I,lk_get hl _ _ (by simp),fun e => ?_⟩,fun _ => trivial⟩
      have hi := lk_get hl (ofString "i") I (by simp)
      have ht := lk_get hl (ofString "t") T (by simp [irP0])
      subst e
      simp [EV,evalHOLExact,evalListHOLExact,hi,ht,wordOpHOL,wordOp,valueIsWord,valueWord,memLoadHOLExact,
        hm.1.2.2.1] at ev
      by_cases hd : s.memaddrs (T + 16#64)
      · simp [hd,Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at ev
        exact nz ev.symm
      · simp [hd] at ev
    · refine aqm_seq (Q := fun _ M => MI P0 T E M0 KL SD C N KS VS US OS OPS M) (aqm_store' _ _ ?_ ?_)
        (aqm_return _ (fun _ _ _ h _ _ => h))
      · intro F s a _ ⟨⟨I,hl,hI,hm⟩,I',hI',hne⟩ _ ev
        have hi := lk_get hl (ofString "i") I (by simp)
        rw [hi] at hI'; cases hI'
        have ht := lk_get hl (ofString "t") T (by simp [irP0])
        simp [EV,evalHOLExact,evalListHOLExact,ht,hi,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,memLoadHOLExact,
          hm.1.2.2.2.2.2.1] at ev
        by_cases hd : s.memaddrs (T + 40#64)
        · simp [hd,valueWord] at ev
          subst ev
          have hlt : I.toNat < C.toNat := by
            have : I.toNat ≠ C.toNat := fun e => hne (BitVec.eq_of_toNat_eq e)
            omega
          obtain ⟨fa,ha⟩ := arr_slot8 lay.valsR lay.eEnd lay.hdrP hlt
          exact ⟨fun e => hw (e ▸ fa),fun y _ => mi_write hm fitT _ fa ha (fun x hx => word_update_keep x hx)⟩
        · simp [hd] at ev
      · intro F s x _ ⟨⟨I,hl,_,_⟩,_⟩ _ ev
        have hv := lk_get hl (ofString "value") V (by simp [irP0])
        simp [EV,evalHOLExact,hv] at ev
        exact ⟨V,ev.symm⟩
  -- grow when the load factor would exceed one half
  refine aqmh_seq (Q := fun L M H => (∃ I : BitVec 64, LK ((ofString "i",I) :: irP0 T Kk V) L) ∧
      SetMid T E M0 C SD KS VS US OS OPS Hc M H)
    (aqmh_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => (N.toNat + 1) * 2 ≤ C.toNat) _ ?_ ?_ ?_) ?_
  · intro F s x H _ ⟨_,I,hl,_,hm⟩ _ ev
    refine ⟨fun _ => trivial,fun hx => ?_⟩
    subst hx
    have ht := lk_get hl (ofString "t") T (by simp [irP0])
    simp [EV,evalHOLExact,evalListHOLExact,ht,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,memLoadHOLExact,
      hm.1.2.2.1,hm.1.2.2.2.1] at ev
    by_cases d16 : s.memaddrs (T + 16#64)
    · by_cases d24 : s.memaddrs (T + 24#64)
      · simp [d16,d24,valueWord,Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at ev
        have e1 : (N + 1#64).toNat = N.toNat + 1 := by rw [BitVec.toNat_add_of_lt (by simp; omega)]; simp
        have e2 : ((N + 1#64) * 2#64).toNat = (N.toNat + 1) * 2 := by
          rw [BitVec.toNat_mul,e1]; exact Nat.mod_eq_of_lt (by simp; omega)
        have := BitVec.le_def.mp ev
        rw [e2] at this
        exact this
      · simp [d16,d24] at ev
    · simp [d16] at ev
  · refine aqmh_callSpec (Vn' := fun _ => True)
      (Pe := fun _ M0' H0 L M H => LK [(ofString "t",T)] L ∧ Hdr M T KL SD C N KS VS US OS OPS ∧ M = M0' ∧ H = H0)
      (RRe := fun _ M0' H0 _ M' H' => ∃ K NKS NVS NUS NOS NOPS H5 : BitVec 64, K.toNat ≤ N.toNat ∧
        P0.toNat ≤ H0.toNat ∧ H0.toNat ≤ H5.toNat ∧ H5.toNat ≤ H'.toNat ∧
        HLay H5 T (GrowFoot T H0) KL SD (C * 2#64) K NKS NVS NUS NOS NOPS (b + 1) ∧
        LayIn (fun x => H0.toNat ≤ x.toNat ∧ x.toNat < H5.toNat) (C * 2#64) SD NKS NVS NUS NOS NOPS ∧
        MI H5 T (GrowFoot T H0) M0' KL SD (C * 2#64) K NKS NVS NUS NOS NOPS M')
      _ _ _ _ _ originalRuntimeCode_hashGrow_lookup (by simp)
      (fun _ M0' H0 _ => grow_aqmh T E KL SD C N KS VS US OS OPS b lay M0' hw H0) ?_ ?_
    · intro F s values callee rs _ H _ ⟨⟨_,I,hl,_,hm⟩,_⟩ _ args lookup
      have ht := lk_get hl (ofString "t") T (by simp [irP0])
      rw [evalListHOLFinite_eq_toExact] at args
      simp [evalListHOLExact,evalHOLExact,ht] at args
      subst args
      rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_hashGrow_lookup] at lookup
      simp only [Option.some.injEq,Prod.mk.injEq] at lookup
      obtain ⟨_,rfl,_⟩ := lookup
      exact ⟨fun p hp => by simp at hp; subst hp; simp [HolFiniteMapExact.lookup_update,FUPDATE],hm.1,rfl,rfl⟩
    · intro L M H v M' H' ⟨⟨hcH,I,hl,_,hm⟩,_⟩ ⟨K,NKS,NVS,NUS,NOS,NOPS,H5,hK,_,h05,h5,hlay,inn,hmi⟩
      have c2 : (C * 2#64).toNat = C.toNat * 2 := by
        rw [BitVec.toNat_mul]; exact Nat.mod_eq_of_lt (by simp; omega)
      refine ⟨⟨I,hl⟩,by omega,fun x hx => ?_,KL,SD,C * 2#64,K,NKS,NVS,NUS,NOS,NOPS,b + 1,
        hlay_canon hlay h5,hmi.1,by rw [c2]; omega,fun x hx => Or.inr (by have := inn x hx; omega)⟩
      have ng : ¬ Foot H5 T (GrowFoot T H) x := by
        rintro (⟨lo,hi⟩ | h)
        · exact hx (lay.hdr x lo hi)
        · exact hx (lay.fresh x (by omega))
      exact (hmi.2 x ng).trans (hm.2 x hx)
  · refine aqmh_conseq (aqmh_of_aqm
      (P := fun H L M => (Hc.toNat ≤ H.toNat ∧ ∃ I : BitVec 64, LK ((ofString "i",I) :: irP0 T Kk V) L ∧
        I.toNat ≤ C.toNat ∧ MI P0 T E M0 KL SD C N KS VS US OS OPS M) ∧ (N.toNat + 1) * 2 ≤ C.toNat)
      (Q := fun H L M => (Hc.toNat ≤ H.toNat ∧ ∃ I : BitVec 64, LK ((ofString "i",I) :: irP0 T Kk V) L ∧
        I.toNat ≤ C.toNat ∧ MI P0 T E M0 KL SD C N KS VS US OS OPS M) ∧ (N.toNat + 1) * 2 ≤ C.toNat)
      (RR := fun _ _ _ => False) (fun H _ => aqm_skip)) (fun _ _ _ h => h) ?_ (fun _ _ _ ⟨_,_,_,f⟩ => f.elim)
    intro L M H' ⟨H,_,hle,⟨hcH,I,hl,_,hm⟩,hg⟩
    exact ⟨⟨I,hl⟩,by omega,hm.2,KL,SD,C,N,KS,VS,US,OS,OPS,b,hlay_canon lay (by omega),hm.1,by omega,
      fun x hx => Or.inl hx⟩
  -- insert into the (possibly grown) table, then return
  refine aqmh_seq (Q := fun _ M H => SetPost T E M0 C SD KS VS US OS OPS Hc M H) (aqmh_callSpec (Vn' := fun _ => True)
      (Pe := fun _ M0' H0 L M H => (∃ Kk V : BitVec 64, LK (irP0 T Kk V) L) ∧ M = M0' ∧ H = H0)
      (RRe := fun _ M0' H0 _ M' H' => H0.toNat ≤ H'.toNat ∧ ∃ (KL' SD' C' N' KS' VS' US' OS' OPS' : BitVec 64) (b' : Nat),
        HLay H0 T (Canon T C' SD' KS' VS' US' OS' OPS' H0) KL' SD' C' N' KS' VS' US' OS' OPS' b' ∧
        N'.toNat + 1 < C'.toNat ∧
        LayIn (fun x => ArrOf C SD KS VS US OS OPS x ∨ (Hc.toNat ≤ x.toNat ∧ x.toNat < H0.toNat))
          C' SD' KS' VS' US' OS' OPS' ∧
        MI H0 T (Canon T C' SD' KS' VS' US' OS' OPS' H0) M0' KL' SD' C' (N' + 1#64) KS' VS' US' OS' OPS' M')
      _ _ _ _ _ originalRuntimeCode_hashInsert_lookup (by simp) ?_ ?_ ?_) (aqmh_return _ (fun _ _ _ _ h _ _ => h))
  · intro L0 M0' H0 ⟨_,hcH,_,KL',SD',C',N',KS',VS',US',OS',OPS',b',hlay,hh,room,inn⟩
    have hwC : ¬ Foot H0 T (Canon T C' SD' KS' VS' US' OS' OPS' H0) w :=
      fun h => hw (canon_sub lay p0 hcH inn w h)
    refine aqmh_conseq (aqmh_of_aqm (P := fun H L M => H = H0 ∧ _) (Q := fun H L M => H = H0 ∧ True)
      (RR := fun H v M => H = H0 ∧ _)
      (fun H _ => aqm_bound_eq (insertRaw_aqm_ex T _ KL' SD' C' N' KS' VS' US' OS' OPS' b' hlay M0' hwC)))
      (fun L M H ⟨h1,h2,h3⟩ => ⟨h3,h1,h2 ▸ hh,h2⟩) (fun _ _ _ _ => trivial) ?_
    intro v M H' ⟨H,_,hle,e,r⟩
    subst e
    exact ⟨hle,KL',SD',C',N',KS',VS',US',OS',OPS',b',hlay,room,inn,r⟩
  · intro F s values callee rs _ H _ ⟨⟨I,hl⟩,_⟩ _ args lookup
    have ht := lk_get hl (ofString "t") T (by simp [irP0])
    have hk := lk_get hl (ofString "key") Kk (by simp [irP0])
    have hv := lk_get hl (ofString "value") V (by simp [irP0])
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,ht,hk,hv] at args
    subst args
    rw [pan_three_word_lookup _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
      originalRuntimeCode_hashInsert_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    refine ⟨⟨Kk,V,fun p hp => ?_⟩,rfl,rfl⟩
    simp only [irP0,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  · intro L M H v M' H' ⟨_,hcH,ag,_⟩ ⟨hle,KL',SD',C',N',KS',VS',US',OS',OPS',b',hlay,room,inn,hmi⟩
    have e1 : (N' + 1#64).toNat = N'.toNat + 1 := by
      have := arr_end hlay.usedR hlay.eEnd
      rw [BitVec.toNat_add_of_lt (by simp; omega)]; simp
    refine ⟨by omega,fun x hx => ?_,KL',SD',C',N' + 1#64,KS',VS',US',OS',OPS',b',
      hlay_canon (hlay_count hlay _ (by rw [e1]; omega)) hle,hmi.1,
      fun x hx => (inn x hx).imp id (fun h => ⟨h.1,by omega⟩)⟩
    exact (hmi.2 x (fun h => hx (canon_sub lay p0 hcH inn x h))).trans (ag x hx)

#print axioms hlay_canon
#print axioms canon_sub
#print axioms set_aqmh
end InitECandidate.Runtime
