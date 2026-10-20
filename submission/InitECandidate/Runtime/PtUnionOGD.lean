import InitECandidate.Runtime.PtTabSet2GD
/-!
Block tables whose values are never written through (`bs + 8 … 48`, the inner storage tables): `TabO O Tt P M` is a
valid `htab` layout at `Tt` (canonical footprint at the bound `P`) with its header in memory, header and arrays inside
the owned region `O`. The actual `htab_set` (heap-aware frame `set_aqmh`, no key premises) keeps it with the owned
region grown by the fresh heap `[Hc, H')`, changing only owned words or words at/above `Hc`. The actual
`htab_union_into(dst, src)` into such a table from any source pointer is the loop of such sets.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A valid table at `Tt` (canonical footprint at `P`), header in memory, header and arrays in `O`. -/
def TabO (O : BitVec 64 → Prop) (Tt P : BitVec 64) (M : Mem) : Prop :=
  ∃ l : TLay, HLay P Tt (Canon Tt l.C l.SD l.KS l.VS l.US l.OS l.OPS P) l.KL l.SD l.C l.N l.KS l.VS l.US l.OS l.OPS l.b ∧
    Hdr M Tt l.KL l.SD l.C l.N l.KS l.VS l.US l.OS l.OPS ∧
    (∀ x : BitVec 64, Tt.toNat ≤ x.toNat → x.toNat < Tt.toNat + 72 → O x) ∧ LayIn O l.C l.SD l.KS l.VS l.US l.OS l.OPS

section tob
variable {O O' : BitVec 64 → Prop} {Tt P : BitVec 64} {M M' : Mem}

theorem tabO_sub (h : TabO O Tt P M) (sub : ∀ x, O x → O' x) : TabO O' Tt P M :=
  let ⟨l,lay,hd,ho,li⟩ := h; ⟨l,lay,hd,fun x a b => sub x (ho x a b),fun x hx => sub x (li x hx)⟩

theorem tabO_mono {P' : BitVec 64} (h : TabO O Tt P M) (le : P.toNat ≤ P'.toNat) : TabO O Tt P' M :=
  let ⟨l,lay,hd,ho,li⟩ := h; ⟨l,hlay_canon lay le,hd,ho,li⟩

theorem tabO_frame (h : TabO O Tt P M) (keep : ∀ x, O x → M' x = M x) : TabO O Tt P M' := by
  obtain ⟨l,lay,hd,ho,li⟩ := h
  have := lay.eEnd
  exact ⟨l,lay,hdr_keep hd (by omega) (fun x lo hi => keep x (ho x lo hi)),ho,li⟩

/-- A set on a `TabO` table: owned region grown by `[Hc, H')`, only owned words or words at/above `Hc` changed. -/
theorem tabO_set {Hc H' : BitVec 64} {l : TLay}
    (ho : ∀ x : BitVec 64, Tt.toNat ≤ x.toNat → x.toNat < Tt.toNat + 72 → O x)
    (li : LayIn O l.C l.SD l.KS l.VS l.US l.OS l.OPS)
    (post : SetPost Tt (Canon Tt l.C l.SD l.KS l.VS l.US l.OS l.OPS Hc) M l.C l.SD l.KS l.VS l.US l.OS l.OPS Hc M' H') :
    TabO (fun x => O x ∨ (Hc.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) Tt H' M' ∧ Hc.toNat ≤ H'.toNat ∧
      ∀ x, ¬ O x → x.toNat < Hc.toNat → M' x = M x := by
  obtain ⟨le,fr,KL',SD',C',N',KS',VS',US',OS',OPS',b',lay',hd',li'⟩ := post
  refine ⟨⟨⟨KL',SD',C',N',KS',VS',US',OS',OPS',b'⟩,lay',hd',fun x a b => Or.inl (ho x a b),fun x hx => ?_⟩,le,
    fun x hx hlt => fr x (fun hc => ?_)⟩
  · rcases li' x hx with h | h
    · exact Or.inl (li x h)
    · exact Or.inr h
  · rcases hc with ⟨lo,hi⟩ | h | h
    · exact hx (ho x lo hi)
    · exact hx (li x h)
    · omega

#print axioms tabO_set
end tob

section un
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM : BitVec 64} {G0 : GA}
  {J C SKB Nj H0 : BitVec 64} {M0 : Mem}

/-- State inside a union into a `TabO` table: heap at least `H0`, the table owned by `O ∪ [H0, H)`, the journal
counter, every word outside `O` below `H0` as in `M0`. -/
def UOS (O : BitVec 64 → Prop) (Td H0 Nj : BitVec 64) (M0 : Mem) (M : Mem) (G : GA) : Prop :=
  ∃ H : BitVec 64, HeapIs G H ∧ H0.toNat ≤ H.toNat ∧
    TabO (fun x => O x ∨ (H0.toNat ≤ x.toNat ∧ x.toNat < H.toNat)) Td H M ∧
    G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∀ x, ¬ O x → x.toNat < H0.toNat → M x = M0 x

/-- One union step `htab_set(dst, s.1, s.2)` on a `TabO` table. -/
theorem unionSetO_aqgd {LP : GA → Prop} {RR : ValueHOL 64 → Mem → GA → Prop} (O : BitVec 64 → Prop) (Td : BitVec 64)
    (hwO : ¬ O w) (hwP : w.toNat < P0.toNat) (p0 : P0.toNat ≤ H0.toNat)
    (hl : ∀ L, LP L → L.lookup (ofString "dst") = some (.val (.word Td)) ∧
      ∃ a b d : BitVec 64, L.lookup (ofString "s") = some (.rStruct [.val (.word a),.val (.word b),.val (.word d)])) :
    AQGD D B (JWS SP0 P0 FM G0 J C SKB) w (fun x => x ≠ ofString "s")
      (fun L M G => LP L ∧ UOS O Td H0 Nj M0 M G) (fun L M G => LP L ∧ UOS O Td H0 Nj M0 M G) RR
      (.call (some (none,none)) (ofString "htab_set")
        [.var .local (ofString "dst"),.rfield 1 (.var .local (ofString "s")),.rfield 2 (.var .local (ofString "s"))]) := by
  refine aqgd_conseq (P := fun L M G => ∃ q : TLay × BitVec 64, LP L ∧ HeapIs G q.2 ∧ H0.toNat ≤ q.2.toNat ∧
      (HLay q.2 Td (Canon Td q.1.C q.1.SD q.1.KS q.1.VS q.1.US q.1.OS q.1.OPS q.2) q.1.KL q.1.SD q.1.C q.1.N q.1.KS
        q.1.VS q.1.US q.1.OS q.1.OPS q.1.b ∧ Hdr M Td q.1.KL q.1.SD q.1.C q.1.N q.1.KS q.1.VS q.1.US q.1.OS q.1.OPS ∧
        (∀ x : BitVec 64, Td.toNat ≤ x.toNat → x.toNat < Td.toNat + 72 →
          O x ∨ (H0.toNat ≤ x.toNat ∧ x.toNat < q.2.toNat)) ∧
        LayIn (fun x => O x ∨ (H0.toNat ≤ x.toNat ∧ x.toNat < q.2.toNat)) q.1.C q.1.SD q.1.KS q.1.VS q.1.US q.1.OS
          q.1.OPS) ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∀ x, ¬ O x → x.toNat < H0.toNat → M x = M0 x)
    (aqgd_ex (fun q => ?_)) (fun L M G ⟨lp,H,hH,hle,⟨l,lay,hd,ho,li⟩,hn,fr⟩ =>
      ⟨(l,H),lp,hH,hle,⟨lay,hd,ho,li⟩,hn,fr⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  rcases q with ⟨l,H⟩
  refine aqgd_callSpec (Vn' := fun _ => True)
    (Pe := fun _ M0' G0' L M G => (∃ K V : BitVec 64, LK (irP0 Td K V) L) ∧ M = M0' ∧ G = G0')
    (RRe := fun _ M0' G0' _ M' G' => G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      ∃ H' : BitVec 64, HeapIs G' H' ∧ SetPost Td (Canon Td l.C l.SD l.KS l.VS l.US l.OS l.OPS H) M0' l.C l.SD l.KS
        l.VS l.US l.OS l.OPS H M' H')
    _ _ _ _ _ originalRuntimeCode_hashSet_lookup (by simp) ?_ ?_ ?_
  · intro L0 M0' G0' ⟨_,hH,hle,⟨lay,hd,ho,li⟩,hn,_⟩
    dsimp only at hle lay hd ho li
    have p2 : P0.toNat ≤ H.toNat := by omega
    have hwk : ¬ Foot H Td (Canon Td l.C l.SD l.KS l.VS l.US l.OS l.OPS H) w := fun hc => by
      unfold Foot at hc
      rcases hc with ⟨lo,hi⟩ | h | h
      · rcases ho w lo hi with h | ⟨h1,_⟩
        · exact hwO h
        · omega
      · rcases li w h with h | ⟨h1,_⟩
        · exact hwO h
        · omega
      · omega
    refine aqgd_conseq (P := fun L M G => ∃ K V : BitVec 64, LK (irP0 Td K V) L ∧ M = M0' ∧ G = G0')
      (aqgd_exE (fun K => aqgd_exE (fun V => aqgd_conseq (aqgd_jws (aqgd_of_aqg (aqg_of_aqmh_j (J := J) (C := C) (N := Nj)
        originalRuntimeCode_hashSet_lookup (by decide_cbv) (by decide_cbv) (by decide_cbv)
        (aqmh_rebound (set_aqmh (P0 := H) Td K V _ l.KL l.SD l.C l.N l.KS l.VS l.US l.OS l.OPS l.b lay M0' hwk H
          (le_refl _)) p2)))
        (keepsSkBuf_of_installed originalRuntimeCode_hashSet_lookup (by decide))) ?_ (fun _ _ _ _ => trivial) ?_)))
      (fun L M G ⟨⟨K,V,hk⟩,hM,hG⟩ => ⟨K,V,hk,hM,hG⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
    · intro L M G ⟨hk,hM,hG⟩
      rw [hM,hG]
      exact ⟨hn,H,hH,le_refl _,hk,hd,rfl,rfl⟩
    · intro v M' G' ⟨hn',H',hH',post⟩
      exact ⟨hn',H',hH',post⟩
  · intro F s values callee rs _ G hG ⟨lp,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨hd,a,b,d,hs⟩ := hl _ lp
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hd,hs] at args
    subst args
    rw [pan_three_word_lookup _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
      originalRuntimeCode_hashSet_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    refine ⟨⟨b,d,fun p hp => ?_⟩,rfl,rfl⟩
    simp only [irP0,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  · intro L M G v M' G' ⟨lp,hH,hle,⟨lay,hd,ho,li⟩,hn,frO⟩ ⟨hn',H',hH',post⟩
    dsimp only at hle lay hd ho li
    obtain ⟨t',le',fr'⟩ := tabO_set ho li post
    refine ⟨lp,H',hH',by omega,tabO_sub t' (fun x h => ?_),hn',fun x hx hlt => ?_⟩
    · rcases h with (h | ⟨h1,h2⟩) | ⟨h1,h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1,by omega⟩
      · exact Or.inr ⟨by omega,h2⟩
    · refine (fr' x (fun h => ?_) (by omega)).trans (frO x hx hlt)
      rcases h with h | ⟨h1,_⟩
      · exact hx h
      · omega

#print axioms unionSetO_aqgd

/-- The actual `htab_union_into(dst, src)` into a `TabO` table `dst = Td`. -/
theorem htabUnionO_aqgd (O : BitVec 64 → Prop) (Td : BitVec 64) (hwO : ¬ O w) (hwP : w.toNat < P0.toNat)
    (p0 : P0.toNat ≤ H0.toNat) :
    AQGD D B (JWS SP0 P0 FM G0 J C SKB) w (fun x => x ≠ ofString "s")
      (fun L M G => UL Td L ∧ TabO O Td H0 M ∧ M = M0 ∧ HeapIs G H0 ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (fun _ _ _ => True) (fun _ M' G' => UOS O Td H0 Nj M0 M' G')
      (sourceFunctionBody Guest.guestFn_htab_union_into) := by
  rw [source_htabUnionInto_body]
  refine aqgd_conseq (P := fun L M G => UL Td L ∧ UOS O Td H0 Nj M0 M G) ?_
    (fun L M G ⟨ul,t,hM,hH,hn⟩ => ⟨ul,H0,hH,le_refl _,tabO_sub t (fun x h => Or.inl h),hn,fun x _ _ => by rw [hM]⟩)
    (fun _ _ _ h => h) (fun _ _ _ h => h)
  refine aqgd_decD (Qb := fun _ _ _ => True) (ofString "cap") .one _ (fun _ => rfl)
    (Pb := fun L M G => UL Td L ∧ UOS O Td H0 Nj M0 M G)
    (fun s v _ _ _ _ ⟨ul,rs⟩ _ _ _ => ⟨ul_upd ul _ v (by decide) (by decide),rs⟩) ?_ (fun _ _ _ _ _ _ _ _ => trivial)
  refine aqgd_decD (Qb := fun _ _ _ => True) (ofString "i") .one _ (fun _ => rfl)
    (Pb := fun L M G => ULi Td L ∧ UOS O Td H0 Nj M0 M G)
    (fun s v _ _ _ _ ⟨ul,rs⟩ _ ev _ => by
      simp [EV,evalHOLExact] at ev; subst ev
      exact ⟨⟨ul_upd ul _ _ (by decide) (by decide),0#64,lookup_update_eq' _ _ _⟩,rs⟩) ?_
    (fun _ _ _ _ _ _ _ _ => trivial)
  refine aqgd_seq (aqgd_whileU _ ?_) (aqgd_return _ (fun _ _ _ _ _ ⟨_,rs⟩ _ _ => rs))
  refine aqgd_decCallSpec (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' _ M G => M = M0' ∧ G = G0') (RRe := fun _ M0' G0' _ M' G' => M' = M0' ∧ G' = G0')
    (Pc := fun L M G => (ULi Td L ∧ ∃ a b d : BitVec 64,
      L.lookup (ofString "s") = some (.rStruct [.val (.word a),.val (.word b),.val (.word d)])) ∧
      UOS O Td H0 Nj M0 M G)
    (Qc := fun L M G => ULi Td L ∧ UOS O Td H0 Nj M0 M G)
    _ _ _ _ _ _ _ originalRuntimeCode_htabItem_lookup (by simp)
    (fun _ M0' G0' _ => aqgd_of_mf htabItem_memoryFrame (by body_check Guest.guestFn_htab_item)
      (by body_check Guest.guestFn_htab_item) M0' G0')
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun h => absurd rfl h) ?_ ?_
    (fun _ _ _ _ _ _ _ ⟨⟨ul,Iv,hi⟩,rs⟩ => ⟨⟨ul_res ul _ _ (by decide) (by decide),Iv,
      by rw [resVar_lookup_ne _ _ _ _ (by decide)]; exact hi⟩,rs⟩)
  · intro L M G v M' G' ⟨⟨⟨ul,Iv,hi⟩,rs⟩,_⟩ ⟨e1,e2⟩ ok
    subst e1 e2
    obtain ⟨a,b,d,rfl⟩ := triple_of_shape ok
    exact ⟨⟨⟨ul_upd ul _ _ (by decide) (by decide),Iv,by rw [lookup_update_ne' _ _ (by decide)]; exact hi⟩,
      a,b,d,lookup_update_eq' _ _ _⟩,rs⟩
  refine aqgd_seq (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
      (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩)
      (aqgd_conseq (unionSetO_aqgd O Td hwO hwP p0 (fun L ⟨⟨ul,_⟩,hs⟩ => ⟨ul.1,hs⟩)) (fun _ _ _ h => h.1)
        (fun _ _ _ h => h) (fun _ _ _ h => h))
      (aqgd_conseq aqgd_skip (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)))
    (aqgd_assignLocal _ _ (fun s v _ _ ⟨⟨⟨ul,Iv,hi⟩,_⟩,rs⟩ _ ev => by
      simp [EV,evalHOLExact,evalListHOLExact,hi,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
      subst ev
      exact ⟨⟨ul_upd ul _ _ (by decide) (by decide),Iv + 1,lookup_update_eq' _ _ _⟩,rs⟩))

#print axioms htabUnionO_aqgd
end un

section uc
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}

/-- The actual `htab_union_into(ed, es)` call into a `TabO` table `Td` (arguments evaluating to `Td` and any word). -/
theorem aqgd_call_unionO {LP : GA → Prop} (ed es : ExpHOL 64) (O : BitVec 64 → Prop) (Td H0 Nj : BitVec 64)
    (M1 : Mem) (G1 : GA) (t : TabO O Td H0 M1) (hH1 : HeapIs G1 H0)
    (hN1 : G1.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (hwO : ¬ O w) (hwP : w.toNat < P0.toNat) (p0 : P0.toNat ≤ H0.toNat)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memaddrs = D → s.memory = M1 → s.globals = G1 →
      LP s.locals → ∃ y : BitVec 64, evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [ed,es] = some [.val (.word Td),.val (.word y)]) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LP L ∧ M = M1 ∧ G = G1) (fun L M G => LP L ∧ UOS O Td H0 Nj M1 M G) RR
      (.call (some (none,none)) (ofString "htab_union_into") [ed,es]) := by
  refine aqgd_callSpecD (Vn' := fun x => x ≠ ofString "s")
    (Pe := fun _ M0' G0' L M G => UL Td L ∧ M = M0' ∧ G = G0')
    (RRe := fun _ M0' _ _ M' G' => UOS O Td H0 Nj M0' M' G')
    _ _ _ _ _ originalRuntimeCode_htabUnionInto_lookup (by simp) ?_ ?_ ?_
  · intro L0 M0' G0' ⟨_,hM,hG⟩
    refine aqgd_jwsbus (U := U) (Bo := Bo) (Sc := Sc) (aqgd_conseq (htabUnionO_aqgd (M0 := M0') (Nj := Nj) O Td hwO hwP p0)
      (fun L M G ⟨ul,hM',hG'⟩ => ⟨ul,by rw [hM',hM]; exact t,hM',by rw [hG',hG]; exact hH1,by rw [hG',hG]; exact hN1⟩)
      (fun _ _ _ _ => trivial) (fun _ _ _ h => h))
      (keepsBo_of_installed originalRuntimeCode_htabUnionInto_lookup (by decide))
      (keepsWs_of_installed originalRuntimeCode_htabUnionInto_lookup (by decide))
      (keepsScr_of_installed originalRuntimeCode_htabUnionInto_lookup (by decide))
  · intro F s values callee rs _ dom G hG ⟨lp,hM,hG1⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨y,ev⟩ := hargs s dom hM hG1 lp
    rw [ev] at args
    simp only [Option.some.injEq] at args
    subst args
    rw [pan_two_word_lookup _ _ _ _ _ _ _ (by decide) originalRuntimeCode_htabUnionInto_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],y,
      by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,hM,_⟩ u
    rw [← hM]
    exact ⟨lp,u⟩

#print axioms aqgd_call_unionO
end uc
end InitECandidate.Runtime
