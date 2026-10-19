import InitECandidate.Runtime.HtabSetArena
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {SP0 P0 FM w : BitVec 64} {G0 : HolFiniteMapExact MlS (ValueHOL 64)} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → Prop}

/-- Some valid table layout with room for one more entry is in memory, agreeing with `M0` outside the footprint. -/
def RoomyLay (P0 T : BitVec 64) (E : BitVec 64 → Prop) (M0 : Mem) (M : Mem) : Prop :=
  ∃ (KL SD C N KS VS US OS OPS : BitVec 64) (b : Nat), HLay P0 T E KL SD C N KS VS US OS OPS b ∧
    MI P0 T E M0 KL SD C N KS VS US OS OPS M ∧ N.toNat + 1 < C.toNat

theorem hlay_count {P0 T : BitVec 64} {E : BitVec 64 → Prop} {KL SD C N KS VS US OS OPS : BitVec 64} {b : Nat}
    (h : HLay P0 T E KL SD C N KS VS US OS OPS b) (N' : BitVec 64) (c : N'.toNat < C.toNat) :
    HLay P0 T E KL SD C N' KS VS US OS OPS b :=
  ⟨h.pow,h.fits,h.sdAl,h.ksAl,h.usAl,c,h.hdr,h.hdrP,h.eEnd,h.fresh,h.keysR,h.valsR,h.usedR,h.orderR,h.oposR⟩

set_option maxHeartbeats 4000000 in
/-- `htab_set` under the real table layout, exporting the post-call layout: every word outside the footprint is
kept in every outcome, and a return leaves a valid layout (count below capacity) in memory, agreeing with the entry
outside the footprint. -/
theorem set_aqm_lay (T Kk V : BitVec 64) (E : BitVec 64 → Prop) (KL SD C N KS VS US OS OPS : BitVec 64) (b : Nat)
    (lay : HLay P0 T E KL SD C N KS VS US OS OPS b) (M0 : Mem) (hw : ¬ Foot P0 T E w) :
    AQM SP0 P0 FM G0 w (fun _ => True)
      (fun L M => LK (irP0 T Kk V) L ∧ Hdr M T KL SD C N KS VS US OS OPS ∧ M = M0)
      (fun _ _ => True) (fun _ M' => AnyLay P0 T E M0 M')
      (sourceFunctionBody Guest.guestFn_htab_set) := by
  have fitT : T.toNat + 72 < 2 ^ 64 := by have := lay.eEnd; omega
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_htab_set,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,List.map_cons,List.map_nil,Option.map_none]
  refine aqm_conseq (P := fun L M => LK (irP0 T Kk V) L ∧ MI P0 T E M0 KL SD C N KS VS US OS OPS M) ?_
    (fun L M h => ⟨h.1,h.2.1,fun x _ => by rw [h.2.2]⟩) (fun _ _ h => h) (fun _ _ h => h)
  -- i = htab_find_slot(t, key)
  refine aqm_decCallSpec (Vn' := fun _ => False)
    (Pe := fun _ M0' L M => L.lookup (ofString "t") = some (.val (.word T)) ∧ M = M0' ∧ M (T + 16) = .word C)
    (RRe := fun _ M0' v M' => M' = M0' ∧ ∃ i : BitVec 64, v = .val (.word i) ∧ i.toNat ≤ C.toNat)
    (Pc := fun L M => ∃ I : BitVec 64, LK ((ofString "i",I) :: irP0 T Kk V) L ∧ I.toNat ≤ C.toNat ∧
      MI P0 T E M0 KL SD C N KS VS US OS OPS M)
    (Qc := fun _ _ => True) _ _ _ _ _ _ _ originalRuntimeCode_hashFind_lookup (by simp)
    (fun _ M0' _ => findSlot_aqm T C b lay.pow M0') ?_ (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ => trivial)
  · intro F s values callee rs _ ⟨hl,hm⟩ _ args lookup
    have ht := lk_get hl (ofString "t") T (by simp [irP0])
    have hk := lk_get hl (ofString "key") Kk (by simp [irP0])
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,ht,hk] at args
    subst args
    rw [pan_two_word_lookup _ _ _ _ _ _ _ (by decide) originalRuntimeCode_hashFind_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],rfl,hm.1.2.2.1⟩
  · intro L M v M' ⟨hl,hm⟩ ⟨eM,I,ev,hI⟩ _
    subst eM ev
    exact ⟨I,lk_cons hl _ _ (by unfold irP0; lkne),hI,hm⟩
  -- found: update the value slot and return
  refine aqm_seq (Q := fun L M => ∃ I : BitVec 64, LK ((ofString "i",I) :: irP0 T Kk V) L ∧ I.toNat ≤ C.toNat ∧
      MI P0 T E M0 KL SD C N KS VS US OS OPS M) (aqm_ite (CT := fun L M => ∃ I : BitVec 64,
      L.lookup (ofString "i") = some (.val (.word I)) ∧ I ≠ C) (CF := fun _ _ => True) _ ?_ ?_
      (aqm_conseq aqm_skip (fun _ _ h => h.1) (fun _ _ h => h) (fun _ _ h => h))) ?_
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
  · refine aqm_seq (Q := fun _ M => AnyLay P0 T E M0 M) (aqm_store' _ _ ?_ ?_) (aqm_return _ (fun _ _ _ h _ _ => h))
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
        exact ⟨fun e => hw (e ▸ fa),fun y _ => ⟨KL,SD,C,N,KS,VS,US,OS,OPS,b,lay,
          mi_write hm fitT _ fa ha (fun x hx => word_update_keep x hx)⟩⟩
      · simp [hd] at ev
    · intro F s x _ ⟨⟨I,hl,_,_⟩,_⟩ _ ev
      have hv := lk_get hl (ofString "value") V (by simp [irP0])
      simp [EV,evalHOLExact,hv] at ev
      exact ⟨V,ev.symm⟩
  -- grow when the load factor would exceed one half
  have cHE : C.toNat ≤ 33806089496 := by have := arr_end lay.usedR lay.eEnd; omega
  have nC := lay.cnt
  refine aqm_seq (Q := fun L M => (∃ I : BitVec 64, LK ((ofString "i",I) :: irP0 T Kk V) L) ∧ RoomyLay P0 T E M0 M)
    (aqm_ite (CT := fun _ _ => True) (CF := fun _ _ => (N.toNat + 1) * 2 ≤ C.toNat) _ ?_ ?_ ?_) ?_
  · intro F s x _ ⟨I,hl,_,hm⟩ _ ev
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
  · refine aqm_callSpec (Vn' := fun _ => True)
      (Pe := fun _ M0' L M => LK [(ofString "t",T)] L ∧ Hdr M T KL SD C N KS VS US OS OPS ∧ M = M0')
      (RRe := fun _ M0' _ M' => ∃ K NKS NVS NUS NOS NOPS : BitVec 64, K.toNat ≤ N.toNat ∧
        HLay P0 T E KL SD (C * 2#64) K NKS NVS NUS NOS NOPS (b + 1) ∧
        MI P0 T E M0' KL SD (C * 2#64) K NKS NVS NUS NOS NOPS M')
      _ _ _ _ _ originalRuntimeCode_hashGrow_lookup (by simp)
      (fun _ M0' _ => grow_aqm T E KL SD C N KS VS US OS OPS b lay M0' hw) ?_ ?_
    · intro F s values callee rs _ ⟨⟨I,hl,_,hm⟩,_⟩ _ args lookup
      have ht := lk_get hl (ofString "t") T (by simp [irP0])
      rw [evalListHOLFinite_eq_toExact] at args
      simp [evalListHOLExact,evalHOLExact,ht] at args
      subst args
      rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_hashGrow_lookup] at lookup
      simp only [Option.some.injEq,Prod.mk.injEq] at lookup
      obtain ⟨_,rfl,_⟩ := lookup
      exact ⟨fun p hp => by simp at hp; subst hp; simp [HolFiniteMapExact.lookup_update,FUPDATE],hm.1,rfl⟩
    · intro L M v M' ⟨⟨I,hl,_,hm⟩,_⟩ ⟨K,NKS,NVS,NUS,NOS,NOPS,hK,hlay,hmi⟩
      have c2 : (C * 2#64).toNat = C.toNat * 2 := by
        rw [BitVec.toNat_mul]; exact Nat.mod_eq_of_lt (by simp; omega)
      exact ⟨⟨I,hl⟩,KL,SD,C * 2#64,K,NKS,NVS,NUS,NOS,NOPS,b + 1,hlay,⟨hmi.1,
        fun x hx => (hmi.2 x hx).trans (hm.2 x hx)⟩,by rw [c2]; omega⟩
  · refine aqm_conseq aqm_skip (fun _ _ h => h) ?_ (fun _ _ h => h)
    intro L M ⟨⟨I,hl,_,hm⟩,hg⟩
    exact ⟨⟨I,hl⟩,KL,SD,C,N,KS,VS,US,OS,OPS,b,lay,hm,by omega⟩
  -- insert into the (possibly grown) table
  refine aqm_seq (Q := fun _ M => AnyLay P0 T E M0 M) (aqm_callSpec (Vn' := fun _ => True)
      (Pe := fun _ M0' L M => (∃ Kk V : BitVec 64, LK (irP0 T Kk V) L) ∧ M = M0')
      (RRe := fun _ M0' _ M' => AnyLay P0 T E M0' M')
      _ _ _ _ _ originalRuntimeCode_hashInsert_lookup (by simp) ?_ ?_ ?_) (aqm_return _ (fun _ _ _ h _ _ => h))
  · intro L0 M0' ⟨_,KL',SD',C',N',KS',VS',US',OS',OPS',b',hlay,hmi,room⟩
    have e1 : (N' + 1#64).toNat = N'.toNat + 1 := by
      have := arr_end hlay.usedR hlay.eEnd
      rw [BitVec.toNat_add_of_lt (by simp; omega)]; simp
    exact aqm_conseq (insertRaw_aqm_ex T E KL' SD' C' N' KS' VS' US' OS' OPS' b' hlay M0' hw)
      (fun L M ⟨h1,h2⟩ => ⟨h1,h2 ▸ hmi.1,h2⟩) (fun _ _ h => h)
      (fun _ M' h => ⟨KL',SD',C',N' + 1#64,KS',VS',US',OS',OPS',b',hlay_count hlay _ (by rw [e1]; omega),h⟩)
  · intro F s values callee rs _ ⟨⟨I,hl⟩,_⟩ _ args lookup
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
    refine ⟨⟨Kk,V,fun p hp => ?_⟩,rfl⟩
    simp only [irP0,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  · intro L M v M' ⟨_,KL',SD',C',N',KS',VS',US',OS',OPS',b',_,hmi,_⟩ ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,hl',hm'⟩
    exact ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,hl',hm'.1,fun x hx => (hm'.2 x hx).trans (hmi.2 x hx)⟩


#print axioms set_aqm_lay
end InitECandidate.Runtime
