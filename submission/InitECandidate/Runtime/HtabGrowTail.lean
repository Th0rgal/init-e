import InitECandidate.Runtime.ArenaHeap
import InitECandidate.Runtime.HtabGrowArena
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-!
Heap-aware pieces of `htab_grow`: the allocator with its exact exit heap pointer, and the post-allocation part of
`htab_grow` (`growTail`) proved against an explicit footprint, so that a caller can choose a precise footprint for the
grown table (header plus the heap above the first allocation).
-/

variable {SP0 P0 FM w : BitVec 64} {G0 : HolFiniteMapExact MlS (ValueHOL 64)} {Vn : MlS → Prop}

/-- Heap-aware `alloc(N)` from heap pointer `Hc`: memory unchanged; a returned block is `Hc` (8-aligned, at or above
`P0`), and the exit heap pointer is `allocationEnd Hc N`, covering `[Hc, Hc + N)`, 8-aligned and below `HEAP_END`. -/
theorem alloc_aqmh (Nn Hc : BitVec 64) (M0 : Mem) :
    AQMH SP0 P0 FM G0 w (fun _ => True)
      (fun L M H => L.lookup (ofString "n") = some (.val (.word Nn)) ∧ M = M0 ∧ H = Hc) (fun _ _ _ => True)
      (fun v M' H' => M' = M0 ∧ v = .val (.word Hc) ∧ H' = allocationEnd Hc Nn ∧ P0.toNat ≤ Hc.toNat ∧
        Hc.toNat + Nn.toNat ≤ H'.toNat ∧ H'.toNat ≤ 33806089496 ∧ H'.toNat % 8 = 0 ∧ Hc.toNat % 8 = 0)
      (sourceFunctionBody Guest.guestFn_alloc) := by
  intro F s code dom aw sl H hH ⟨hn,hm,hc⟩
  subst hc
  obtain ⟨m,a,n,c,b⟩ := alloc_aq (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (w := w) F s code dom aw sl trivial
  refine ⟨m,a,fun e => ⟨(n e).1,?_⟩,fun v e => ?_,c,b⟩
  · obtain ⟨_,_,⟨hp,hhp,_,_,_⟩,_⟩ := a (Or.inl e)
    exact ⟨hp,hhp,trivial⟩
  · obtain ⟨_,_,⟨hp,hhp,lo,hi,al⟩,_⟩ := aw
    have eq : hp = H := by
      unfold HeapIs at hH; rw [hhp] at hH; simpa using hH
    subst eq
    obtain ⟨req,fin,ew,mem,_,_,_,gl⟩ := alloc_body_returned s _ hp Nn code hhp hn v (Prod.ext e rfl)
    have sb := allocationGuard_sum_bound hp Nn hi req
    obtain ⟨c1,_,c3⟩ := allocationEnd_covers hp Nn sb
    refine ⟨allocationEnd hp Nn,?_,by rw [mem,hm],ew,rfl,lo,c1,fin,c3,al⟩
    unfold HeapIs; rw [gl]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

/-- The part of `htab_grow` after its five allocations: clear the new used bytes, write the new header, rehash. -/
def growTail : ProgHOL 64 :=
  ((ProgHOL.call (some (none, none)) (ofString "memzero") [ExpHOL.var VarKind.local (ofString "nused"), ExpHOL.var VarKind.local (ofString "ncap")]).seq ((ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "t"), ExpHOL.const 16#64]) (ExpHOL.var VarKind.local (ofString "ncap"))).seq ((ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "t"), ExpHOL.const 32#64]) (ExpHOL.var VarKind.local (ofString "nkeys"))).seq ((ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "t"), ExpHOL.const 40#64]) (ExpHOL.var VarKind.local (ofString "nvals"))).seq ((ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "t"), ExpHOL.const 48#64]) (ExpHOL.var VarKind.local (ofString "nused"))).seq ((ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "t"), ExpHOL.const 56#64]) (ExpHOL.var VarKind.local (ofString "norder"))).seq ((ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "t"), ExpHOL.const 64#64]) (ExpHOL.var VarKind.local (ofString "norder_pos"))).seq ((ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "t"), ExpHOL.const 24#64]) (ExpHOL.const 0#64)).seq (ProgHOL.dec (ofString "k") ShapeHOL.one (ExpHOL.const 0#64) ((ProgHOL.while (ExpHOL.cmp Cmp.less (ExpHOL.var VarKind.local (ofString "k")) (ExpHOL.var VarKind.local (ofString "nitems"))) (ProgHOL.dec (ofString "i") ShapeHOL.one (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "order"), ExpHOL.panop PanOp.mul [ExpHOL.var VarKind.local (ofString "k"), ExpHOL.const 8#64]])) ((ProgHOL.call (some (none, none)) (ofString "htab_insert_raw") [ExpHOL.var VarKind.local (ofString "t"), ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "keys"), ExpHOL.panop PanOp.mul [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.var VarKind.local (ofString "stride")]], ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "vals"), ExpHOL.panop PanOp.mul [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 8#64]])]).seq (ProgHOL.assign VarKind.local (ofString "k") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "k"), ExpHOL.const 1#64]))))).seq (ProgHOL.return (ExpHOL.const 0#64))))))))))))

set_option maxHeartbeats 4000000 in
/-- `htab_grow` after its allocations, against an explicit footprint `E`: the new arrays are given by `newLay`, the
new used-byte block lies inside `E` (above the header) and above the watched word. -/
theorem growTail_aqm (T : BitVec 64) (E : BitVec 64 → Prop)
    (KL SD C N KS VS US OS OPS NKS NVS NUS NOS NOPS : BitVec 64) (b : Nat) (M0 : Mem)
    (fitT : T.toNat + 72 < 2 ^ 64) (cHE : C.toNat ≤ 33806089496) (nC : N.toNat < C.toNat)
    (hdr : ∀ x : BitVec 64, T.toNat ≤ x.toNat → x.toNat < T.toNat + 72 → E x) (hw : ¬ Foot P0 T E w)
    (usAl : NUS.toNat % 8 = 0) (usFit : NUS.toNat + C.toNat * 2 ≤ 33806089496) (hwU : w.toNat < NUS.toNat)
    (usWin : ∀ x : BitVec 64, NUS.toNat ≤ x.toNat → x.toNat < NUS.toNat + (C * 2#64).toNat →
      Foot P0 T E x ∧ T.toNat + 72 ≤ x.toNat)
    (newLay : ∀ K : BitVec 64, K.toNat ≤ N.toNat → HLay P0 T E KL SD (C * 2#64) K NKS NVS NUS NOS NOPS (b + 1)) :
    AQM SP0 P0 FM G0 w (fun _ => True)
      (fun L M => LK ((ofString "norder_pos",NOPS) :: (ofString "norder",NOS) :: (ofString "nused",NUS) :: (ofString "nvals",NVS) :: (ofString "nkeys",NKS) :: grP T C SD KS VS OS N) L ∧ MI P0 T E M0 KL SD C N KS VS US OS OPS M)
      (fun _ _ => True)
      (fun _ M' => ∃ K : BitVec 64, K.toNat ≤ N.toNat ∧
        HLay P0 T E KL SD (C * 2#64) K NKS NVS NUS NOS NOPS (b + 1) ∧
        MI P0 T E M0 KL SD (C * 2#64) K NKS NVS NUS NOS NOPS M')
      growTail := by
  have c2 : (C * 2#64).toNat = C.toNat * 2 := by
    rw [BitVec.toNat_mul]; exact Nat.mod_eq_of_lt (by simp; omega)
  unfold growTail
  refine aqm_seq (Q := HW P0 T E M0 ((ofString "norder_pos",NOPS) :: (ofString "norder",NOS) :: (ofString "nused",NUS) :: (ofString "nvals",NVS) :: (ofString "nkeys",NKS) :: grP T C SD KS VS OS N) [(8#64,SD),(0#64,KL)]) (aqm_callSpec (Vn' := fun _ => False)
    (Pe := fun _ M0' L M => L.lookup (ofString "dst") = some (.val (.word NUS)) ∧
      L.lookup (ofString "n") = some (.val (.word (C * 2#64))) ∧ M = M0')
    (RRe := fun _ M0' _ M' => ∀ x, ¬ MWin NUS (C * 2#64).toNat x → M' x = M0' x)
    _ _ _ _ _ originalRuntimeCode_memzero_lookup (by simp)
    (fun _ M0' _ => memzero_aqm NUS (C * 2#64) (by omega) (mwin_above hwU usAl (by omega)) M0') ?_ ?_) ?_
  · intro F s values callee rs _ ⟨hl,_⟩ _ args lookup
    have h1 := lk_get hl (ofString "nused") NUS (by simp)
    have h2 := lk_get hl (ofString "ncap") (C * 2#64) (by simp [grP])
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,h1,h2] at args
    subst args
    rw [pan_two_word_lookup _ _ _ _ _ _ _ (by decide) originalRuntimeCode_memzero_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
      by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl⟩
  · intro L M v M' ⟨hl,hm⟩ h
    have hm' := mi_frame hm fitT (MWin NUS (C * 2#64).toNat) (fun x hx => by
      obtain ⟨lo,hi⟩ := mwin_ge hx usAl (by omega)
      exact usWin x lo hi) h
    refine ⟨hl,fun p hp => ?_,hm'.2⟩
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl | rfl
    · exact hm'.1.2.1
    · exact hm'.1.1
  refine aqm_seq (aqm_cellStore 16#64 (C * 2#64) _ (by simp [grP]) (by decide) hdr fitT hw
    (by simp) (fun s x hl ev => by
      have h := lk_get hl (ofString "ncap") (C * 2#64) (by simp [grP])
      simp [EV,evalHOLExact,h] at ev; exact ev.symm)) ?_
  refine aqm_seq (aqm_cellStore 32#64 (NKS) _ (by simp [grP]) (by decide) hdr fitT hw
    (by simp) (fun s x hl ev => by
      have h := lk_get hl (ofString "nkeys") (NKS) (by simp [grP])
      simp [EV,evalHOLExact,h] at ev; exact ev.symm)) ?_
  refine aqm_seq (aqm_cellStore 40#64 (NVS) _ (by simp [grP]) (by decide) hdr fitT hw
    (by simp) (fun s x hl ev => by
      have h := lk_get hl (ofString "nvals") (NVS) (by simp [grP])
      simp [EV,evalHOLExact,h] at ev; exact ev.symm)) ?_
  refine aqm_seq (aqm_cellStore 48#64 (NUS) _ (by simp [grP]) (by decide) hdr fitT hw
    (by simp) (fun s x hl ev => by
      have h := lk_get hl (ofString "nused") (NUS) (by simp [grP])
      simp [EV,evalHOLExact,h] at ev; exact ev.symm)) ?_
  refine aqm_seq (aqm_cellStore 56#64 (NOS) _ (by simp [grP]) (by decide) hdr fitT hw
    (by simp) (fun s x hl ev => by
      have h := lk_get hl (ofString "norder") (NOS) (by simp [grP])
      simp [EV,evalHOLExact,h] at ev; exact ev.symm)) ?_
  refine aqm_seq (aqm_cellStore 64#64 (NOPS) _ (by simp [grP]) (by decide) hdr fitT hw
    (by simp) (fun s x hl ev => by
      have h := lk_get hl (ofString "norder_pos") (NOPS) (by simp [grP])
      simp [EV,evalHOLExact,h] at ev; exact ev.symm)) ?_
  refine aqm_seq (aqm_cellStore 24#64 (0#64) _ (by simp [grP]) (by decide) hdr fitT hw
    (by simp) (fun s x hl ev => by simp [EV,evalHOLExact] at ev; exact ev.symm)) ?_
  refine aqm_dec (Pb := fun L M => ∃ K : BitVec 64, LK ((ofString "k",K) :: ((ofString "norder_pos",NOPS) :: (ofString "norder",NOS) :: (ofString "nused",NUS) :: (ofString "nvals",NVS) :: (ofString "nkeys",NKS) :: grP T C SD KS VS OS N)) L ∧ K.toNat ≤ N.toNat ∧
      Hdr M T KL SD (C * 2#64) K NKS NVS NUS NOS NOPS ∧ ∀ x, ¬ Foot P0 T E x → M x = M0 x) (Qb := fun _ _ => True) _ _ _ (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ => trivial)
  · intro F s v _ ⟨hl,hc,ag⟩ _ ev _
    simp [EV,evalHOLExact] at ev
    subst ev
    exact ⟨0#64,lk_cons hl _ _ (by unfold grP; lkne),by simp,cells_hdr hc,ag⟩
  refine aqm_seq (Q := fun L M => ∃ K : BitVec 64, LK ((ofString "k",K) :: ((ofString "norder_pos",NOPS) :: (ofString "norder",NOS) :: (ofString "nused",NUS) :: (ofString "nvals",NVS) :: (ofString "nkeys",NKS) :: grP T C SD KS VS OS N)) L ∧ K.toNat ≤ N.toNat ∧
      Hdr M T KL SD (C * 2#64) K NKS NVS NUS NOS NOPS ∧ ∀ x, ¬ Foot P0 T E x → M x = M0 x)
    (aqm_while (C := fun L M => ∃ K : BitVec 64, L.lookup (ofString "k") = some (.val (.word K)) ∧ K.toNat < N.toNat)
      _ ?_ ?_) (aqm_return _ ?_)
  · intro F s x _ ⟨K,hl,hK,_⟩ _ ev nz
    have h1 := lk_get hl (ofString "k") K (by simp)
    have h2 := lk_get hl (ofString "nitems") N (by simp [grP])
    simp [EV,evalHOLExact,h1,h2] at ev
    have small : K.toNat < 2 ^ 63 ∧ N.toNat < 2 ^ 63 := by constructor <;> omega
    rw [Flapjack.Compiler.Encoders.Asm.wordCmpHOL,holAsmSignedLess_small K N small.1 small.2] at ev
    refine ⟨K,h1,?_⟩
    by_contra hge
    simp [hge] at ev
    exact nz ev.symm
  · refine aqm_dec (Pb := fun L M => ∃ I K : BitVec 64, LK ((ofString "i",I) :: (ofString "k",K) :: ((ofString "norder_pos",NOPS) :: (ofString "norder",NOS) :: (ofString "nused",NUS) :: (ofString "nvals",NVS) :: (ofString "nkeys",NKS) :: grP T C SD KS VS OS N)) L ∧ K.toNat < N.toNat ∧
      Hdr M T KL SD (C * 2#64) K NKS NVS NUS NOS NOPS ∧ ∀ x, ¬ Foot P0 T E x → M x = M0 x) (Qb := fun L M => ∃ K : BitVec 64, LK ((ofString "k",K) :: ((ofString "norder_pos",NOPS) :: (ofString "norder",NOS) :: (ofString "nused",NUS) :: (ofString "nvals",NVS) :: (ofString "nkeys",NKS) :: grP T C SD KS VS OS N)) L ∧ K.toNat ≤ N.toNat ∧
      Hdr M T KL SD (C * 2#64) K NKS NVS NUS NOS NOPS ∧ ∀ x, ¬ Foot P0 T E x → M x = M0 x) _ _ _ (fun _ => rfl) ?_ ?_ ?_
    · intro F s v _ ⟨⟨K,hl,_,hh,ag⟩,K',hk',hlt⟩ _ ev _
      have h1 := lk_get hl (ofString "k") K (by simp)
      rw [h1] at hk'; cases hk'
      obtain ⟨y,rfl⟩ := ev_load_one_word s _ v ev
      exact ⟨y,K,lk_cons hl _ _ (by unfold grP; lkne),hlt,hh,ag⟩
    · refine aqm_seq (Q := fun L M => ∃ I K : BitVec 64, LK ((ofString "i",I) :: (ofString "k",K) :: ((ofString "norder_pos",NOPS) :: (ofString "norder",NOS) :: (ofString "nused",NUS) :: (ofString "nvals",NVS) :: (ofString "nkeys",NKS) :: grP T C SD KS VS OS N)) L ∧ K.toNat < N.toNat ∧
      Hdr M T KL SD (C * 2#64) (K + 1#64) NKS NVS NUS NOS NOPS ∧ ∀ x, ¬ Foot P0 T E x → M x = M0 x) (aqm_callSpec (Vn' := fun _ => True)
        (Pe := fun _ M0' L M => (∃ Kk V : BitVec 64, LK (irP0 T Kk V) L) ∧ M = M0')
        (RRe := fun _ M0' _ M' => ∀ K : BitVec 64, M0' (T + 24#64) = .word K →
          MI P0 T E M0' KL SD (C * 2#64) (K + 1#64) NKS NVS NUS NOS NOPS M')
        _ _ _ _ _ originalRuntimeCode_hashInsert_lookup (by simp) ?_ ?_ ?_) (aqm_assignLocal _ _ ?_)
      · intro L0 M0' ⟨I,K,hl,hK,hh,ag⟩
        refine aqm_conseq (insertRaw_aqm_ex T E KL SD (C * 2#64) K NKS NVS NUS NOS NOPS (b + 1)
          (newLay K (by omega)) M0' hw) (fun L M ⟨h1,h2⟩ => ⟨h1,h2 ▸ hh,h2⟩) (fun _ _ h => h) ?_
        intro v M' h K' hK'
        rw [hh.2.2.2.1] at hK'
        simp only [HolWordLab.word.injEq] at hK'
        subst hK'
        exact h
      · intro F s values callee rs _ ⟨I,K,hl,_,_⟩ _ args lookup
        have ht := lk_get hl (ofString "t") T (by simp [grP])
        have hks := lk_get hl (ofString "keys") KS (by simp [grP])
        have hi := lk_get hl (ofString "i") I (by simp)
        have hsd := lk_get hl (ofString "stride") SD (by simp [grP])
        have hvs := lk_get hl (ofString "vals") VS (by simp [grP])
        rw [evalListHOLFinite_eq_toExact] at args
        cases hx : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
            (.load .one (.op .add [.var .local (ofString "vals"),.panop .mul [.var .local (ofString "i"),.const 8#64]])) with
        | none => simp [evalListHOLExact,hx] at args
        | some x =>
          obtain ⟨y,rfl⟩ := ev_load_one_word s _ x hx
          simp only [evalListHOLExact] at args
          rw [hx] at args
          simp [evalListHOLExact,evalHOLExact,ht,hks,hi,hsd,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord] at args
          subst args
          rw [pan_three_word_lookup _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
            originalRuntimeCode_hashInsert_lookup] at lookup
          simp only [Option.some.injEq,Prod.mk.injEq] at lookup
          obtain ⟨_,rfl,_⟩ := lookup
          refine ⟨⟨KS + I * SD,y,fun p hp => ?_⟩,rfl⟩
          simp only [irP0,List.mem_cons,List.mem_nil_iff,or_false] at hp
          rcases hp with rfl | rfl | rfl <;>
            simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
      · intro L M v M' ⟨I,K,hl,hK,hh,ag⟩ h
        have := h K hh.2.2.2.1
        exact ⟨I,K,hl,hK,this.1,fun x hx => (this.2 x hx).trans (ag x hx)⟩
      · intro F s v _ ⟨I,K,hl,hK,hh,ag⟩ _ ev
        have h1 := lk_get hl (ofString "k") K (by simp)
        simp [EV,evalHOLExact,evalListHOLExact,h1,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
        subst ev
        refine ⟨K + 1#64,lk_cons (fun p hp => hl p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))) _ _
          (by unfold grP; lkne),?_,hh,ag⟩
        rw [BitVec.toNat_add_of_lt (by simp; omega)]; simp; omega
    · intro L M L' M' _ h
      obtain ⟨K,hl,hK,hh,ag⟩ := h
      exact ⟨K,lk_res hl _ _ (by unfold grP; lkne),hK,hh,ag⟩
  · intro F s v _ ⟨K,_,hK,hh,ag⟩ _ _
    exact ⟨K,hK,newLay K hK,hh,ag⟩

#print axioms alloc_aqmh
#print axioms growTail_aqm
end InitECandidate.Runtime
