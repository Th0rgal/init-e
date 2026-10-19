import InitECandidate.Runtime.HtabGrowArena
import InitECandidate.Runtime.OriginalHashGrowCode
import InitECandidate.Runtime.OriginalHashFindCode
import InitECandidate.Runtime.OriginalHashSetCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {SP0 P0 FM w : BitVec 64} {G0 : HolFiniteMapExact MlS (ValueHOL 64)} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → Prop}

/-- Some valid table layout is in memory, agreeing with `M0` outside the footprint. -/
def AnyLay (P0 T E : BitVec 64) (M0 : Mem) (M : Mem) : Prop :=
  ∃ (KL SD C N KS VS US OS OPS : BitVec 64) (b : Nat), HLay P0 T E KL SD C N KS VS US OS OPS b ∧
    MI P0 T E M0 KL SD C N KS VS US OS OPS M

set_option maxHeartbeats 4000000 in
/-- `htab_set` under the real table layout: every word outside the footprint is kept in every outcome, and a
return leaves memory agreeing with the entry outside the footprint. -/
theorem set_aqm (T Kk V E KL SD C N KS VS US OS OPS : BitVec 64) (b : Nat)
    (lay : HLay P0 T E KL SD C N KS VS US OS OPS b) (M0 : Mem) (hw : ¬ Foot P0 T E w) :
    AQM SP0 P0 FM G0 w (fun _ => True)
      (fun L M => LK (irP0 T Kk V) L ∧ Hdr M T KL SD C N KS VS US OS OPS ∧ M = M0)
      (fun _ _ => True) (fun _ M' => ∀ x, ¬ Foot P0 T E x → M' x = M0 x)
      (sourceFunctionBody Guest.guestFn_htab_set) := by
  have fitT : T.toNat + 72 < 2 ^ 64 := by have := lay.hdr; have := lay.eEnd; omega
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
  · refine aqm_seq (Q := fun _ M => ∀ x, ¬ Foot P0 T E x → M x = M0 x) (aqm_store' _ _ ?_ ?_) (aqm_return _ (fun _ _ _ h _ _ => h))
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
        refine ⟨fun e => hw (e ▸ fa),fun y _ x hx => ?_⟩
        have : x ≠ VS + I * 8#64 := fun e => hx (e ▸ fa)
        simp only [if_neg this]
        exact hm.2 x hx
      · simp [hd] at ev
    · intro F s x _ ⟨⟨I,hl,_,_⟩,_⟩ _ ev
      have hv := lk_get hl (ofString "value") V (by simp [irP0])
      simp [EV,evalHOLExact,hv] at ev
      exact ⟨V,ev.symm⟩
  -- grow when the load factor would exceed one half
  refine aqm_seq (Q := fun L M => (∃ I : BitVec 64, LK ((ofString "i",I) :: irP0 T Kk V) L) ∧ AnyLay P0 T E M0 M) (aqm_ite (CT := fun _ _ => True) (CF := fun _ _ => True) _
      (fun _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) ?_ ?_) ?_
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
    · intro L M v M' ⟨⟨I,hl,_,hm⟩,_⟩ ⟨K,NKS,NVS,NUS,NOS,NOPS,_,hlay,hmi⟩
      exact ⟨⟨I,hl⟩,KL,SD,C * 2#64,K,NKS,NVS,NUS,NOS,NOPS,b + 1,hlay,hmi.1,
        fun x hx => (hmi.2 x hx).trans (hm.2 x hx)⟩
  · refine aqm_conseq aqm_skip (fun _ _ h => h) ?_ (fun _ _ h => h)
    intro L M ⟨⟨I,hl,_,hm⟩,_⟩
    exact ⟨⟨I,hl⟩,KL,SD,C,N,KS,VS,US,OS,OPS,b,lay,hm⟩
  -- insert into the (possibly grown) table
  refine aqm_seq (Q := fun _ M => ∀ x, ¬ Foot P0 T E x → M x = M0 x) (aqm_callSpec (Vn' := fun _ => True)
      (Pe := fun _ M0' L M => (∃ Kk V : BitVec 64, LK (irP0 T Kk V) L) ∧ M = M0')
      (RRe := fun _ M0' _ M' => ∀ x, ¬ Foot P0 T E x → M' x = M0' x)
      _ _ _ _ _ originalRuntimeCode_hashInsert_lookup (by simp) ?_ ?_ ?_) (aqm_return _ (fun _ _ _ h _ _ => h))
  · intro L0 M0' ⟨_,KL',SD',C',N',KS',VS',US',OS',OPS',b',hlay,hmi⟩
    exact aqm_conseq (insertRaw_aqm_ex T E KL' SD' C' N' KS' VS' US' OS' OPS' b' hlay M0' hw)
      (fun L M ⟨h1,h2⟩ => ⟨h1,h2 ▸ hmi.1,h2⟩) (fun _ _ h => h) (fun _ _ h => h.2)
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
  · intro L M v M' ⟨_,KL',SD',C',N',KS',VS',US',OS',OPS',b',_,hmi⟩ h x hx
    exact (h x hx).trans (hmi.2 x hx)


#print axioms set_aqm
end InitECandidate.Runtime
