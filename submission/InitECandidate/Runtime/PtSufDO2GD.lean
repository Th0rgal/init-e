import InitECandidate.Runtime.PtLstB2GD
/-!
The block-list section of the `process_transaction` suffix (spine drops 120-126, `PtSufDOGD`) over the arena with the
`bal_*` globals pinned (`JWB`): the same actual statements, the list calls re-derived, the store leaves lifted.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section l1b
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc Hb Nj : BitVec 64} {M0 : Mem} {W40 W72 : BitVec 64 → Prop} {Y : BitVec 64}
  {BA IA IS KB Ixb : BitVec 64}

/-- The first-loop body: `slot = lst_push(lds(bo + 40), 8); st slot, lds(lp + i * 8); i = i + 1`. -/
theorem loop1BodyO2 (bk : BalKeep2) (Ix Nl Lp L40 L72 Iv N : BitVec 64)
    (hW40 : ∀ x, W40 x → BW n c Out Excl w x)
    (hdis : ∀ x, W40 x → ¬ W72 x) (hH40 : ∀ x, HdW L40 x → W40 x) (hOut : Out w)
    (hB40 : Out (Bo + 40#64) ∧ ¬ Excl (Bo + 40#64) ∧ M0 (Bo + 40#64) = .word L40)
    (hg : Nl.toNat < 2 ^ 63 ∧ Iv.toNat < Nl.toNat) :
    AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (I1sO Y n c T Out ko D B Excl Hb Nj M0 W40 W72 Ix Nl Lp L40 L72 Iv N)
      (fun L M G => ∃ Iv' N' : BitVec 64, I1sO Y n c T Out ko D B Excl Hb Nj M0 W40 W72 Ix Nl Lp L40 L72 Iv' N' L M G) RR
      (.decCall (ofString "slot") .one (ofString "lst_push")
        [.load .one (.op .add [.var .global (ofString "bo"),.const 40#64]),.const 8#64]
        (.seq (.store (.var .local (ofString "slot"))
            (.load .one (.op .add [.var .local (ofString "lp"),.panop .mul [.var .local (ofString "i"),.const 8#64]])))
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1#64])))) := by
  refine aqgd_decCall_lstPush_pbB bk (Wb := W40) (R := BL W72 Hb L72 8#64)
    (LP := fun L => (LDnO Y Ix Nl Lp L ∧ L.lookup (ofString "i") = some (.val (.word Iv))) ∧ C1 Nl Iv N)
    (LP' := fun L => (LDnO Y Ix Nl Lp L ∧ L.lookup (ofString "i") = some (.val (.word Iv))) ∧ C1 Nl Iv N)
    (Q := fun L M G => ∃ Iv' N' : BitVec 64, I1sO Y n c T Out ko D B Excl Hb Nj M0 W40 W72 Ix Nl Lp L40 L72 Iv' N' L M G)
    (ofString "slot") 40#64 8#64 L40 N hW40 hOut hB40 (by decide)
    (fun L v ⟨⟨ld,hi⟩,c1⟩ => ⟨⟨ldn_updO ld _ v (by decide) (by decide) (by decide) (by decide),
      by rw [lookup_update_ne' _ _ (by decide)]; exact hi⟩,c1⟩)
    (fun M M' G G' H H' b72 hH hbH hH' le keep => bl_frame b72
      (fun x hx => keep x (by have := hdw_lt b72.2.1 hx; omega) (fun h40 => hdis x (hH40 x h40) (b72.1 x hx)))
      (fun H2 h2 => ⟨H',hH',by have := heapIs_unique hH h2; subst this; exact le⟩)) (fun S => ?_) ?_
  · have hR' : ∀ (M M' : Mem) (G : GA),
        ((BL W40 Hb L40 8#64 M G ∧ M (L40 + 8#64) = .word (N + 1#64) ∧ N.toNat + 1 < 2 ^ 64) ∧
          BL W72 Hb L72 8#64 M G) → ((W40 S ∧ ¬ HdW L40 S) ∨ Hb.toNat ≤ S.toNat) → (∀ x, x ≠ S → M' x = M x) →
        ((BL W40 Hb L40 8#64 M' G ∧ M' (L40 + 8#64) = .word (N + 1#64) ∧ N.toNat + 1 < 2 ^ 64) ∧
          BL W72 Hb L72 8#64 M' G) := by
      intro M M' G ⟨⟨b40,cnt,nb⟩,b72⟩ hS keep
      have k40 : ∀ x, HdW L40 x → M' x = M x := fun x hx => keep x (fun e => by
        subst e
        rcases hS with ⟨_,h⟩ | h
        · exact h hx
        · have := hdw_lt b40.2.1 hx; omega)
      refine ⟨⟨bl_frame b40 k40 (fun H h => ⟨H,h,le_refl _⟩),(k40 _ (Or.inr (Or.inl rfl))).trans cnt,nb⟩,
        bl_frame b72 (fun x hx => keep x (fun e => ?_)) (fun H h => ⟨H,h,le_refl _⟩)⟩
      subst e
      rcases hS with ⟨h,_⟩ | h
      · exact hdis x h (b72.1 x hx)
      · have := hdw_lt b72.2.1 hx; omega
    refine aqgd_seq (aqgd_conseq (aqgd_liftB bk (by simp [keepsG,balWatched]) <| aqgd_store_slot (LP := fun L => (LDnO Y Ix Nl Lp L ∧
        L.lookup (ofString "i") = some (.val (.word Iv))) ∧ C1 Nl Iv N) (Wb := W40)
        (R := fun M G => (BL W40 Hb L40 8#64 M G ∧ M (L40 + 8#64) = .word (N + 1#64) ∧ N.toNat + 1 < 2 ^ 64) ∧
          BL W72 Hb L72 8#64 M G) (ofString "slot") _ S L40 8#64 (by decide) hW40 hOut
        (fun s x _ ev => isWord_load s _ x ev) hR')
      (fun L M G ⟨⟨⟨lp,hS⟩,pb⟩,bl,slot,b72⟩ => ⟨⟨⟨lp,hS⟩,pb⟩,slot,bl,b72⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)) ?_
    refine aqgd_assignLocal _ _ (fun s v _ _ ⟨⟨⟨ld,hi⟩,hc1,_⟩,pb,⟨b40,cnt,nb⟩,b72⟩ _ ev => ?_)
    simp [EV,evalHOLExact,evalListHOLExact,hi,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
    subst ev
    have eI : (Iv + 1#64).toNat = Iv.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    have eN : (N + 1#64).toNat = N.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    refine ⟨Iv + 1#64,N + 1#64,⟨⟨⟨ldn_updO ld _ _ (by decide) (by decide) (by decide) (by decide),
      lookup_update_eq' _ _ _⟩,⟨by rw [eI,eN]; exact Nat.succ_le_succ hc1,Or.inr ⟨by omega,hg.1⟩⟩⟩,pb⟩,⟨b40,cnt⟩,b72⟩
  · intro L M G L' M' G' _ ⟨Iv',N',⟨⟨⟨ld,hi⟩,c1⟩,pb⟩,b40,b72⟩
    exact ⟨Iv',N',⟨⟨⟨ldn_resO ld _ _ (by decide) (by decide) (by decide) (by decide),
      by rw [resVarEq_lookup_ne' _ _ _ _ (by decide)]; exact hi⟩,c1⟩,pb⟩,b40,b72⟩

#print axioms loop1BodyO2

/-- The first loop `while i < nl { ... }`; on exit a nonnegative `nl` is at most the block-list count. -/
theorem loop1O2 (bk : BalKeep2) (Ix Nl Lp L40 L72 : BitVec 64)
    (hW40 : ∀ x, W40 x → BW n c Out Excl w x)
    (hdis : ∀ x, W40 x → ¬ W72 x) (hH40 : ∀ x, HdW L40 x → W40 x) (hOut : Out w)
    (hB40 : Out (Bo + 40#64) ∧ ¬ Excl (Bo + 40#64) ∧ M0 (Bo + 40#64) = .word L40) :
    AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => ∃ Iv N : BitVec 64, I1sO Y n c T Out ko D B Excl Hb Nj M0 W40 W72 Ix Nl Lp L40 L72 Iv N L M G)
      (fun L M G => ∃ Iv N : BitVec 64, I1sO Y n c T Out ko D B Excl Hb Nj M0 W40 W72 Ix Nl Lp L40 L72 Iv N L M G ∧
        (Nl.toNat < 2 ^ 63 → 8 * Nl.toNat < 2 ^ 64)) RR
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
        (.decCall (ofString "slot") .one (ofString "lst_push")
          [.load .one (.op .add [.var .global (ofString "bo"),.const 40#64]),.const 8#64]
          (.seq (.store (.var .local (ofString "slot"))
              (.load .one (.op .add [.var .local (ofString "lp"),.panop .mul [.var .local (ofString "i"),.const 8#64]])))
            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1#64]))))) := by
  refine aqgd_conseq (aqgd_whileE (Qb := fun _ _ _ => False)
    (C := fun L _ _ => ∀ Iv : BitVec 64, L.lookup (ofString "i") = some (.val (.word Iv)) →
      Nl.toNat < 2 ^ 63 ∧ Iv.toNat < Nl.toNat)
    (E := fun L _ _ => ∀ Iv : BitVec 64, L.lookup (ofString "i") = some (.val (.word Iv)) →
      ¬ (Nl.toNat < 2 ^ 63 ∧ Iv.toNat < Nl.toNat)) _ ?_ ?_ ?_) (fun _ _ _ h => h) ?_ (fun _ _ _ h => h)
  · intro F s x _ _ ⟨Iv,N,hiv⟩ _ ev hx Iv' hi'
    have sm := i1_smallO hiv
    obtain ⟨⟨⟨⟨⟨_,hnl⟩,hi⟩,_⟩,_⟩,_⟩ := hiv
    rw [hi] at hi'
    simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at hi'
    subst hi'
    simp [EV,evalHOLExact,hi,hnl (ofString "nl",Nl) (by simp),slt_small (b := Nl) (show Iv.toNat < 2 ^ 63 by omega)]
      at ev
    split at ev
    · rename_i h; exact ⟨by omega,h.2⟩
    · exact absurd ev.symm hx
  · intro F s x _ _ ⟨Iv,N,hiv⟩ _ ev hx Iv' hi'
    have sm := i1_smallO hiv
    obtain ⟨⟨⟨⟨⟨_,hnl⟩,hi⟩,_⟩,_⟩,_⟩ := hiv
    rw [hi] at hi'
    simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at hi'
    subst hi'
    simp [EV,evalHOLExact,hi,hnl (ofString "nl",Nl) (by simp),slt_small (b := Nl) (show Iv.toNat < 2 ^ 63 by omega)]
      at ev
    intro hc
    split at ev
    · subst ev; exact absurd hx (by decide)
    · rename_i h; exact h ⟨by omega,hc.2⟩
  · refine aqgb_of_aqgd (aqgd_conseq (P := fun L M G => ∃ Iv N : BitVec 64,
      I1sO Y n c T Out ko D B Excl Hb Nj M0 W40 W72 Ix Nl Lp L40 L72 Iv N L M G ∧
        (Nl.toNat < 2 ^ 63 ∧ Iv.toNat < Nl.toNat))
      (aqgd_exE (fun Iv => aqgd_exE (fun N => aqgd_pureE (fun hg =>
        loop1BodyO2 bk Ix Nl Lp L40 L72 Iv N hW40 hdis hH40 hOut hB40 hg))))
      (fun L M G ⟨⟨Iv,N,hiv⟩,hc⟩ => ⟨Iv,N,hiv,hc Iv hiv.1.1.1.2⟩) (fun _ _ _ h => h) (fun _ _ _ h => h))
  · intro L M G h
    rcases h with ⟨⟨Iv,N,hiv⟩,he⟩ | h
    · refine ⟨Iv,N,hiv,fun hnl => ?_⟩
      have sm := i1_smallO hiv
      have ne := he Iv hiv.1.1.1.2
      rcases hiv.1.1.2.2 with rfl | ⟨le,_⟩
      · have : Nl.toNat = 0 := by
          by_contra h0
          exact ne ⟨hnl,by simp; omega⟩
        omega
      · have : Nl.toNat ≤ Iv.toNat := by
          by_contra h0
          exact ne ⟨hnl,by omega⟩
        omega
    · exact h.elim

#print axioms loop1O2

/-- The second loop `while i < nl { st stable_lp + i * 8, lds(lp + i * 8); i = i + 1 }` into the fresh buffer at
`Sp ≥ Hb` (`Sp + 8·Nl < 2^64` for a nonnegative `Nl`). -/
theorem loop2O2 (bk : BalKeep2) {R : Mem → GA → Prop} {LE : GA → Prop} (Ix Nl Lp Sp : BitVec 64) (hOut : Out w)
    (hLE : ∀ L v, LE L → LE (L.update (ofString "i",v))) (hSp : Hb.toNat ≤ Sp.toNat)
    (hfit : Nl.toNat < 2 ^ 63 → Sp.toNat + 8 * Nl.toNat < 2 ^ 64)
    (hR : ∀ (M M' : Mem) (G : GA) (a : BitVec 64), R M G → Hb.toNat ≤ a.toNat → (∀ x, x ≠ a → M' x = M x) →
      R M' G) :
    AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => ∃ Iv : BitVec 64, I2sO Y n c T Out ko D B Excl Hb Nj M0 R LE Ix Nl Lp Sp Iv L M G)
      (fun L M G => ∃ Iv : BitVec 64, I2sO Y n c T Out ko D B Excl Hb Nj M0 R LE Ix Nl Lp Sp Iv L M G) RR
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
        (.seq (.store (.op .add [.var .local (ofString "stable_lp"),.panop .mul [.var .local (ofString "i"),.const 8#64]])
            (.load .one (.op .add [.var .local (ofString "lp"),.panop .mul [.var .local (ofString "i"),.const 8#64]])))
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1#64])))) := by
  refine aqgd_conseq (aqgd_whileE (Qb := fun _ _ _ => False) (E := fun _ _ _ => True)
    (C := fun L _ _ => ∀ Iv : BitVec 64, L.lookup (ofString "i") = some (.val (.word Iv)) →
      Nl.toNat < 2 ^ 63 ∧ Iv.toNat < Nl.toNat) _ ?_ (fun _ _ _ _ _ _ _ _ => trivial) ?_)
    (fun _ _ _ h => h) (fun _ _ _ h => by rcases h with ⟨h,_⟩ | h; exact h; exact h.elim) (fun _ _ _ h => h)
  · intro F s x _ _ ⟨Iv,hiv⟩ _ ev hx Iv' hi'
    have sm := i2_smallO hiv
    obtain ⟨⟨⟨⟨⟨⟨_,hnl⟩,_⟩,hi⟩,_⟩,_⟩,_⟩ := hiv
    rw [hi] at hi'
    simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at hi'
    subst hi'
    simp [EV,evalHOLExact,hi,hnl (ofString "nl",Nl) (by simp),slt_small (b := Nl) sm] at ev
    split at ev
    · rename_i h; exact ⟨by omega,h.2⟩
    · exact absurd ev.symm hx
  · refine aqgb_of_aqgd (aqgd_conseq (P := fun L M G => ∃ Iv : BitVec 64,
      I2sO Y n c T Out ko D B Excl Hb Nj M0 R LE Ix Nl Lp Sp Iv L M G ∧ (Nl.toNat < 2 ^ 63 ∧ Iv.toNat < Nl.toNat))
      (aqgd_exE (fun Iv => aqgd_pureE (fun hg => ?_)))
      (fun L M G ⟨⟨Iv,hiv⟩,hc⟩ => ⟨Iv,hiv,hc Iv hiv.1.1.1.2⟩) (fun _ _ _ h => h) (fun _ _ _ h => h))
    have fit := hfit hg.1
    have e8 : (Iv * 8#64).toNat = Iv.toNat * 8 := mul_nat (by simp; omega)
    have ea : (Sp + Iv * 8#64).toNat = Sp.toNat + Iv.toNat * 8 := by
      rw [BitVec.toNat_add,e8]; exact Nat.mod_eq_of_lt (by omega)
    refine aqgd_seq (aqgd_conseq (aqgd_liftB bk (by simp [keepsG,balWatched]) <| aqgd_store_fresh (LP := fun L => ((LDnO Y Ix Nl Lp L ∧ LE L ∧
        L.lookup (ofString "stable_lp") = some (.val (.word Sp))) ∧ L.lookup (ofString "i") = some (.val (.word Iv))) ∧
        (Iv = 0#64 ∨ (Iv.toNat ≤ Nl.toNat ∧ Nl.toNat < 2 ^ 63))) (R := R) _ _ (Sp + Iv * 8#64) hOut
        (fun s lp => by simp [EV,evalHOLExact,evalListHOLExact,lp.1.1.2.2,lp.1.2,wordOpHOL,wordOp,valueIsWord,
          valueWord,panOpHOL])
        (by omega) (fun s x _ ev => isWord_load s _ x ev) (fun M M' G r keep => hR M M' G _ r (by omega) keep))
      (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h)) ?_
    refine aqgd_assignLocal _ _ (fun s v _ _ ⟨⟨⟨⟨⟨ld,le,hs⟩,hi⟩,_⟩,pb⟩,r⟩ _ ev => ?_)
    simp [EV,evalHOLExact,evalListHOLExact,hi,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
    subst ev
    have eI : (Iv + 1#64).toNat = Iv.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    exact ⟨Iv + 1#64,⟨⟨⟨⟨ldn_updO ld _ _ (by decide) (by decide) (by decide) (by decide),hLE _ _ le,
      by rw [lookup_update_ne' _ _ (by decide)]; exact hs⟩,lookup_update_eq' _ _ _⟩,Or.inr ⟨by omega,hg.1⟩⟩,pb⟩,r⟩

#print axioms loop2O2

/-- `rl = lst_push(lds(bo + 72), 8); st rl, stable_logs; rest`. -/
theorem ptSufD_rlO2 (bk : BalKeep2) {Q : GA → Mem → GA → Prop} (Ix Nl Lp L40 L72 X : BitVec 64) {rest : ProgHOL 64}
    (hW72 : ∀ x, W72 x → BW n c Out Excl w x) (hdis : ∀ x, W40 x → ¬ W72 x) (hH40 : ∀ x, HdW L40 x → W40 x)
    (hH72 : ∀ x, HdW L72 x → W72 x) (hOut : Out w)
    (hB72 : Out (Bo + 72#64) ∧ ¬ Excl (Bo + 72#64) ∧ M0 (Bo + 72#64) = .word L72)
    (hQ : ∀ L M G o, Q L M G → Q (L.resVarEq (ofString "rl",o)) M G)
    (hrest : AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => (LDnO Y Ix Nl Lp L ∧ PB n c T Out ko D B Excl Hb Nj M0 M G) ∧
        BL W40 Hb L40 8#64 M G ∧ BL W72 Hb L72 8#64 M G) Q RR rest) :
    AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => ((LDnO Y Ix Nl Lp L ∧ L.lookup (ofString "stable_logs") = some (.val (.word X))) ∧
        PB n c T Out ko D B Excl Hb Nj M0 M G) ∧ BL W40 Hb L40 8#64 M G ∧ BL W72 Hb L72 8#64 M G) Q RR
      (.decCall (ofString "rl") .one (ofString "lst_push")
        [.load .one (.op .add [.var .global (ofString "bo"),.const 72#64]),.const 8#64]
        (.seq (.store (.var .local (ofString "rl")) (.var .local (ofString "stable_logs"))) rest)) := by
  have k40 : ∀ (M M' : Mem) (G G' : GA) (H H' : BitVec 64), BL W40 Hb L40 8#64 M G → HeapIs G H →
      Hb.toNat ≤ H.toNat → HeapIs G' H' → H.toNat ≤ H'.toNat →
      (∀ x, x.toNat < H.toNat → ¬ HdW L72 x → M' x = M x) → BL W40 Hb L40 8#64 M' G' :=
    fun M M' G G' H H' b40 hH hbH hH' le keep => bl_frame b40
      (fun x hx => keep x (by have := hdw_lt b40.2.1 hx; omega) (fun h72 => hdis x (hH40 x hx) (hH72 x h72)))
      (fun H2 h2 => ⟨H',hH',by have := heapIs_unique hH h2; subst this; exact le⟩)
  refine aqgd_conseq (P := fun L M G => ∃ N72 : BitVec 64, ((LDnO Y Ix Nl Lp L ∧
      L.lookup (ofString "stable_logs") = some (.val (.word X))) ∧ PB n c T Out ko D B Excl Hb Nj M0 M G) ∧
      (BL W72 Hb L72 8#64 M G ∧ M (L72 + 8#64) = .word N72) ∧ BL W40 Hb L40 8#64 M G) ?_
    (fun L M G ⟨lp,b40,b72⟩ => let ⟨N72,h⟩ := bl_cnt b72; ⟨N72,lp,⟨b72,h⟩,b40⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  refine aqgd_exE (fun N72 => aqgd_decCall_lstPush_pbB bk (Wb := W72) (R := BL W40 Hb L40 8#64)
    (LP := fun L => LDnO Y Ix Nl Lp L ∧ L.lookup (ofString "stable_logs") = some (.val (.word X)))
    (LP' := fun L => LDnO Y Ix Nl Lp L ∧ L.lookup (ofString "stable_logs") = some (.val (.word X)))
    (ofString "rl") 72#64 8#64 L72 N72 hW72 hOut hB72 (by decide)
    (fun L v ⟨ld,hx⟩ => ⟨ldn_updO ld _ v (by decide) (by decide) (by decide) (by decide),
      by rw [lookup_update_ne' _ _ (by decide)]; exact hx⟩) k40 (fun S => ?_) (fun _ _ _ _ _ _ _ q => hQ _ _ _ _ q))
  have hR' : ∀ (M M' : Mem) (G : GA),
      (BL W72 Hb L72 8#64 M G ∧ BL W40 Hb L40 8#64 M G) → ((W72 S ∧ ¬ HdW L72 S) ∨ Hb.toNat ≤ S.toNat) →
      (∀ x, x ≠ S → M' x = M x) → BL W72 Hb L72 8#64 M' G ∧ BL W40 Hb L40 8#64 M' G := by
    intro M M' G ⟨b72,b40⟩ hS keep
    refine ⟨bl_frame b72 (fun x hx => keep x (fun e => ?_)) (fun H h => ⟨H,h,le_refl _⟩),
      bl_frame b40 (fun x hx => keep x (fun e => ?_)) (fun H h => ⟨H,h,le_refl _⟩)⟩
    · subst e
      rcases hS with ⟨_,h⟩ | h
      · exact h hx
      · have := hdw_lt b72.2.1 hx; omega
    · subst e
      rcases hS with ⟨h,_⟩ | h
      · exact hdis x (hH40 x hx) h
      · have := hdw_lt b40.2.1 hx; omega
  refine aqgd_seq (aqgd_conseq (aqgd_liftB bk (by simp [keepsG,balWatched]) <| aqgd_store_slot (LP := fun L => LDnO Y Ix Nl Lp L ∧
      L.lookup (ofString "stable_logs") = some (.val (.word X))) (Wb := W72)
      (R := fun M G => BL W72 Hb L72 8#64 M G ∧ BL W40 Hb L40 8#64 M G) (ofString "rl") _ S L72 8#64 (by decide)
      hW72 hOut (fun s x lp ev => by simp [EV,evalHOLExact,lp.2] at ev; exact ⟨_,ev.symm⟩) hR')
    (fun L M G ⟨⟨⟨lp,hS⟩,pb⟩,⟨b72,_⟩,slot,b40⟩ => ⟨⟨⟨lp,hS⟩,pb⟩,slot,b72,b40⟩) (fun _ _ _ h => h)
    (fun _ _ _ h => h)) ?_
  exact aqgd_conseq hrest (fun L M G ⟨⟨ld,_⟩,pb,b72,b40⟩ => ⟨⟨ld,pb⟩,b40,b72⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)

#print axioms ptSufD_rlO2

/-- `st stable_logs + 8, nl; stable_lp = lds(stable_logs + 0); i = 0; <second loop>; <rl push>; rest`. -/
theorem ptSufD_slO2 (bk : BalKeep2) {QM : Mem → GA → Prop} (Ix Nl Lp L40 L72 Cs X Pp : BitVec 64) {rest : ProgHOL 64}
    (hW72 : ∀ x, W72 x → BW n c Out Excl w x) (hdis : ∀ x, W40 x → ¬ W72 x) (hH40 : ∀ x, HdW L40 x → W40 x)
    (hH72 : ∀ x, HdW L72 x → W72 x) (hOut : Out w)
    (hB72 : Out (Bo + 72#64) ∧ ¬ Excl (Bo + 72#64) ∧ M0 (Bo + 72#64) = .word L72)
    (hCs : (Nl = 0#64 ∧ Cs = 1#64) ∨ (Nl ≠ 0#64 ∧ Cs = Nl)) (hbd : Nl.toNat < 2 ^ 63 → 8 * Nl.toNat < 2 ^ 64)
    (hX : Hb.toNat ≤ X.toNat) (hXP : X.toNat + 24 ≤ Pp.toNat) (hPC : Pp.toNat + (8#64 * Cs).toNat < 2 ^ 64)
    (hrest : AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => (LDnO Y Ix Nl Lp L ∧ PB n c T Out ko D B Excl Hb Nj M0 M G) ∧
        BL W40 Hb L40 8#64 M G ∧ BL W72 Hb L72 8#64 M G) (fun _ M G => QM M G) RR rest) :
    AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => ((LDnO Y Ix Nl Lp L ∧ L.lookup (ofString "stable_logs") = some (.val (.word X))) ∧
        PB n c T Out ko D B Excl Hb Nj M0 M G) ∧ (BL W40 Hb L40 8#64 M G ∧ BL W72 Hb L72 8#64 M G) ∧ M X = .word Pp)
      (fun _ M G => QM M G) RR
      (.seq (.store (.op .add [.var .local (ofString "stable_logs"),.const 8#64]) (.var .local (ofString "nl")))
        (.dec (ofString "stable_lp") .one (.load .one (.op .add [.var .local (ofString "stable_logs"),.const 0#64]))
          (.seq (.assign .local (ofString "i") (.const 0#64))
            (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
                (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
                    .panop .mul [.var .local (ofString "i"),.const 8#64]])
                  (.load .one (.op .add [.var .local (ofString "lp"),.panop .mul [.var .local (ofString "i"),.const 8#64]])))
                  (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1#64]))))
              (.decCall (ofString "rl") .one (ofString "lst_push")
                [.load .one (.op .add [.var .global (ofString "bo"),.const 72#64]),.const 8#64]
                (.seq (.store (.var .local (ofString "rl")) (.var .local (ofString "stable_logs"))) rest)))))) := by
  have e8 : (X + 8#64).toNat = X.toNat + 8 := by
    rw [BitVec.toNat_add]; have : Pp.toNat < 2 ^ 64 := Pp.isLt; simp; omega
  have hfit : Nl.toNat < 2 ^ 63 → Pp.toNat + 8 * Nl.toNat < 2 ^ 64 := by
    intro h
    rcases hCs with ⟨rfl,_⟩ | ⟨_,rfl⟩
    · simp; exact Pp.isLt
    · have := hbd h
      have e : (8#64 * Cs).toNat = 8 * Cs.toNat := by rw [mul_nat (by simp; omega)]; simp
      omega
  refine aqgd_seq (aqgd_liftB bk (by simp [keepsG,balWatched]) <| aqgd_store_fresh (LP := fun L => LDnO Y Ix Nl Lp L ∧
      L.lookup (ofString "stable_logs") = some (.val (.word X)))
    (R := fun M G => (BL W40 Hb L40 8#64 M G ∧ BL W72 Hb L72 8#64 M G) ∧ M X = .word Pp) _ _ (X + 8#64) hOut
    (fun s lp => ev_addc s _ X 8#64 lp.2) (by omega)
    (fun s x lp ev => by simp [EV,evalHOLExact,lp.1.2 (ofString "nl",Nl) (by simp)] at ev; exact ⟨_,ev.symm⟩)
    (fun M M' G ⟨bls,hp⟩ keep => ⟨bls_fresh bls (by omega) keep,
      (keep X (fun e => by have := congrArg BitVec.toNat e; omega)).trans hp⟩)) ?_
  refine aqgd_decD (Qb := fun _ M G => QM M G) (ofString "stable_lp") .one _ (fun h => h.elim)
    (Pb := fun L M G => ((LDnO Y Ix Nl Lp L ∧ L.lookup (ofString "stable_logs") = some (.val (.word X)) ∧
      L.lookup (ofString "stable_lp") = some (.val (.word Pp))) ∧ PB n c T Out ko D B Excl Hb Nj M0 M G) ∧
      BL W40 Hb L40 8#64 M G ∧ BL W72 Hb L72 8#64 M G) ?_ ?_ (fun _ _ _ _ _ _ _ h => h)
  · intro F s v _ _ _ _ ⟨⟨⟨ld,hx⟩,pb⟩,bls,hp⟩ _ ev _
    rw [ev_load_off s _ X 0#64 v hx ev]
    simp only [BitVec.add_zero,hp]
    exact ⟨⟨⟨ldn_updO ld _ _ (by decide) (by decide) (by decide) (by decide),
      by rw [lookup_update_ne' _ _ (by decide)]; exact hx,lookup_update_eq' _ _ _⟩,pb⟩,bls⟩
  refine aqgd_seq (aqgd_assignLocal (Q := fun L M G => ∃ Iv : BitVec 64,
      I2sO Y n c T Out ko D B Excl Hb Nj M0 (fun M G => BL W40 Hb L40 8#64 M G ∧ BL W72 Hb L72 8#64 M G)
        (fun L => L.lookup (ofString "stable_logs") = some (.val (.word X))) Ix Nl Lp Pp Iv L M G) _ _
      (fun s v _ _ ⟨⟨⟨ld,hx,hs⟩,pb⟩,bls⟩ _ ev => ?_)) ?_
  · simp [EV,evalHOLExact] at ev; subst ev
    exact ⟨0#64,⟨⟨⟨⟨ldn_updO ld _ _ (by decide) (by decide) (by decide) (by decide),
      by beta_reduce; rw [lookup_update_ne' _ _ (by decide)]; exact hx,
      by rw [lookup_update_ne' _ _ (by decide)]; exact hs⟩,
      lookup_update_eq' _ _ _⟩,Or.inl rfl⟩,pb⟩,bls⟩
  refine aqgd_seq (loop2O2 bk Ix Nl Lp Pp hOut (fun L v h => by rw [lookup_update_ne' _ _ (by decide)]; exact h)
    (by omega) hfit (fun M M' G a bls ha keep => bls_fresh bls ha keep)) ?_
  exact aqgd_conseq (ptSufD_rlO2 bk Ix Nl Lp L40 L72 X hW72 hdis hH40 hH72 hOut hB72 (fun _ _ _ _ q => q) hrest)
    (fun L M G ⟨Iv,⟨⟨⟨⟨ld,hx,_⟩,_⟩,_⟩,pb⟩,bls⟩ => ⟨⟨⟨ld,hx⟩,pb⟩,bls⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)

#print axioms ptSufD_slO2

/-- `stable_log_cap = nl; if stable_log_cap == 0 { stable_log_cap = 1 }; stable_logs = lst_new(8, stable_log_cap);
...`. -/
theorem ptSufD_capO2 (bk : BalKeep2) {QM : Mem → GA → Prop} (Ix Nl Lp L40 L72 : BitVec 64) {rest : ProgHOL 64}
    (hW72 : ∀ x, W72 x → BW n c Out Excl w x) (hdis : ∀ x, W40 x → ¬ W72 x) (hH40 : ∀ x, HdW L40 x → W40 x)
    (hH72 : ∀ x, HdW L72 x → W72 x) (hOut : Out w)
    (hB72 : Out (Bo + 72#64) ∧ ¬ Excl (Bo + 72#64) ∧ M0 (Bo + 72#64) = .word L72)
    (hbd : Nl.toNat < 2 ^ 63 → 8 * Nl.toNat < 2 ^ 64)
    (hrest : AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => (LDnO Y Ix Nl Lp L ∧ PB n c T Out ko D B Excl Hb Nj M0 M G) ∧
        BL W40 Hb L40 8#64 M G ∧ BL W72 Hb L72 8#64 M G) (fun _ M G => QM M G) RR rest) :
    AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => (LDnO Y Ix Nl Lp L ∧ PB n c T Out ko D B Excl Hb Nj M0 M G) ∧
        BL W40 Hb L40 8#64 M G ∧ BL W72 Hb L72 8#64 M G) (fun _ M G => QM M G) RR
      (.dec (ofString "stable_log_cap") .one (.var .local (ofString "nl"))
        (.seq (.ite (.cmp .equal (.var .local (ofString "stable_log_cap")) (.const 0#64))
            (.assign .local (ofString "stable_log_cap") (.const 1#64)) .skip)
          (.decCall (ofString "stable_logs") .one (ofString "lst_new")
            [.const 8#64,.var .local (ofString "stable_log_cap")]
            (.seq (.store (.op .add [.var .local (ofString "stable_logs"),.const 8#64]) (.var .local (ofString "nl")))
              (.dec (ofString "stable_lp") .one
                (.load .one (.op .add [.var .local (ofString "stable_logs"),.const 0#64]))
                (.seq (.assign .local (ofString "i") (.const 0#64))
                  (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
                      (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
                          .panop .mul [.var .local (ofString "i"),.const 8#64]])
                        (.load .one (.op .add [.var .local (ofString "lp"),
                          .panop .mul [.var .local (ofString "i"),.const 8#64]])))
                        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1#64]))))
                    (.decCall (ofString "rl") .one (ofString "lst_push")
                      [.load .one (.op .add [.var .global (ofString "bo"),.const 72#64]),.const 8#64]
                      (.seq (.store (.var .local (ofString "rl")) (.var .local (ofString "stable_logs"))) rest))))))))) := by
  refine aqgd_decD (Qb := fun _ M G => QM M G) (ofString "stable_log_cap") .one _ (fun h => h.elim)
    (Pb := fun L M G => ((LDnO Y Ix Nl Lp L ∧ L.lookup (ofString "stable_log_cap") = some (.val (.word Nl))) ∧
      PB n c T Out ko D B Excl Hb Nj M0 M G) ∧ BL W40 Hb L40 8#64 M G ∧ BL W72 Hb L72 8#64 M G) ?_ ?_
    (fun _ _ _ _ _ _ _ h => h)
  · intro F s v _ _ _ _ ⟨⟨ld,pb⟩,bls⟩ _ ev _
    simp [EV,evalHOLExact,ld.2 (ofString "nl",Nl) (by simp)] at ev; subst ev
    exact ⟨⟨⟨ldn_updO ld _ _ (by decide) (by decide) (by decide) (by decide),lookup_update_eq' _ _ _⟩,pb⟩,bls⟩
  refine aqgd_seq (Q := fun L M G => ∃ Cs : BitVec 64, ((((LDnO Y Ix Nl Lp L ∧
      L.lookup (ofString "stable_log_cap") = some (.val (.word Cs))) ∧ PB n c T Out ko D B Excl Hb Nj M0 M G) ∧
      BL W40 Hb L40 8#64 M G ∧ BL W72 Hb L72 8#64 M G) ∧ ((Nl = 0#64 ∧ Cs = 1#64) ∨ (Nl ≠ 0#64 ∧ Cs = Nl)))) ?_ ?_
  · refine aqgd_iteD (CT := fun _ _ _ => Nl = 0#64) (CF := fun _ _ _ => Nl ≠ 0#64) _ ?_ ?_
      (aqgd_conseq aqgd_skip (fun _ _ _ h => h) (fun L M G ⟨p,ne⟩ => ⟨Nl,p,Or.inr ⟨ne,rfl⟩⟩) (fun _ _ _ h => h))
    · intro F s x _ _ _ _ ⟨⟨⟨_,hc⟩,_⟩,_⟩ _ ev
      simp [EV,evalHOLExact,hc] at ev
      simp only [Compiler.Encoders.Asm.wordCmpHOL] at ev
      by_cases e : Nl = 0#64
      · subst e; simp at ev; subst ev; exact ⟨fun _ => rfl,fun h => absurd h (by decide)⟩
      · simp [e] at ev; subst ev; exact ⟨fun h => absurd rfl h,fun _ => e⟩
    · exact aqgd_assignLocal _ _ (fun s v _ _ ⟨⟨⟨⟨ld,_⟩,pb⟩,bls⟩,e⟩ _ ev => by
        simp [EV,evalHOLExact] at ev; subst ev
        exact ⟨1#64,⟨⟨⟨ldn_updO ld _ _ (by decide) (by decide) (by decide) (by decide),lookup_update_eq' _ _ _⟩,pb⟩,
          bls⟩,Or.inl ⟨e,rfl⟩⟩)
  refine aqgd_exE (fun Cs => aqgd_pureE (fun hCs => ?_))
  refine aqgd_decCall_lstNewC_pbB bk (R := fun M G => BL W40 Hb L40 8#64 M G ∧ BL W72 Hb L72 8#64 M G)
    (LP := fun L => LDnO Y Ix Nl Lp L ∧ L.lookup (ofString "stable_log_cap") = some (.val (.word Cs)))
    (LP' := fun L => LDnO Y Ix Nl Lp L) (Q := fun _ M G => QM M G)
    (ofString "stable_logs") (ofString "stable_log_cap") 8#64 Cs hOut (fun L lp => lp.2)
    (fun L v lp => ldn_updO lp.1 _ v (by decide) (by decide) (by decide) (by decide))
    (fun M M' G G' H H' bls hH hbH hH' le keep => ⟨bl_frame bls.1
        (fun x hx => keep x (by have := hdw_lt bls.1.2.1 hx; omega))
        (fun H2 h2 => ⟨H',hH',by have := heapIs_unique hH h2; subst this; exact le⟩),
      bl_frame bls.2 (fun x hx => keep x (by have := hdw_lt bls.2.2.1 hx; omega))
        (fun H2 h2 => ⟨H',hH',by have := heapIs_unique hH h2; subst this; exact le⟩)⟩)
    (fun X Pp => ?_) (fun _ _ _ _ _ _ _ h => h)
  refine aqgd_of_arenaFact (Φ := Hb.toNat ≤ X.toNat ∧ X.toNat + 24 ≤ Pp.toNat ∧
      Pp.toNat + (8#64 * Cs).toNat < 2 ^ 64)
    (fun _ _ _ _ ⟨_,hX,hXP,_,H,_,hPH⟩ => ⟨hX,hXP,by have := H.isLt; omega⟩) ?_
  intro ⟨hX,hXP,hPC⟩
  exact aqgd_conseq (ptSufD_slO2 bk Ix Nl Lp L40 L72 Cs X Pp hW72 hdis hH40 hH72 hOut hB72 hCs hbd hX hXP hPC hrest)
    (fun L M G ⟨⟨⟨⟨ld,hx⟩,pb⟩,bls⟩,_,_,hd,_⟩ => ⟨⟨⟨ld,hx⟩,pb⟩,bls,hd.1⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)

#print axioms ptSufD_capO2

/-- Spine drop 126 of `process_transaction` up to the block-list pushes, for any continuation `rest` (from
`del = lds(out + 24)` on): `nl`, `lp` are interpreter data; the suffix state `PB` and both block lists are kept. -/
theorem ptSufD_headO2 (bk : BalKeep2) {QM : Mem → GA → Prop} (Ix L40 L72 : BitVec 64) {rest : ProgHOL 64}
    (hW40 : ∀ x, W40 x → BW n c Out Excl w x) (hW72 : ∀ x, W72 x → BW n c Out Excl w x)
    (hdis : ∀ x, W40 x → ¬ W72 x) (hH40 : ∀ x, HdW L40 x → W40 x) (hH72 : ∀ x, HdW L72 x → W72 x) (hOut : Out w)
    (hB40 : Out (Bo + 40#64) ∧ ¬ Excl (Bo + 40#64) ∧ M0 (Bo + 40#64) = .word L40)
    (hB72 : Out (Bo + 72#64) ∧ ¬ Excl (Bo + 72#64) ∧ M0 (Bo + 72#64) = .word L72)
    (hrest : ∀ Nl Lp : BitVec 64, AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => (LDnO Y Ix Nl Lp L ∧ PB n c T Out ko D B Excl Hb Nj M0 M G) ∧
        BL W40 Hb L40 8#64 M G ∧ BL W72 Hb L72 8#64 M G) (fun _ M G => QM M G) RR rest) :
    AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ixb) w (fun _ => False)
      (fun L M G => (LPSo Y Ix L ∧ PB n c T Out ko D B Excl Hb Nj M0 M G) ∧
        BL W40 Hb L40 8#64 M G ∧ BL W72 Hb L72 8#64 M G) (fun _ M G => QM M G) RR
      (.dec (ofString "nl") .one (.load .one (.op .add [.var .local (ofString "logs"),.const 8#64]))
        (.dec (ofString "lp") .one (.load .one (.op .add [.var .local (ofString "logs"),.const 0#64]))
          (.seq (.assign .local (ofString "i") (.const 0#64))
            (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
                (.decCall (ofString "slot") .one (ofString "lst_push")
                  [.load .one (.op .add [.var .global (ofString "bo"),.const 40#64]),.const 8#64]
                  (.seq (.store (.var .local (ofString "slot"))
                      (.load .one (.op .add [.var .local (ofString "lp"),
                        .panop .mul [.var .local (ofString "i"),.const 8#64]])))
                    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1#64])))))
              (.dec (ofString "stable_log_cap") .one (.var .local (ofString "nl"))
        (.seq (.ite (.cmp .equal (.var .local (ofString "stable_log_cap")) (.const 0#64))
            (.assign .local (ofString "stable_log_cap") (.const 1#64)) .skip)
          (.decCall (ofString "stable_logs") .one (ofString "lst_new")
            [.const 8#64,.var .local (ofString "stable_log_cap")]
            (.seq (.store (.op .add [.var .local (ofString "stable_logs"),.const 8#64]) (.var .local (ofString "nl")))
              (.dec (ofString "stable_lp") .one
                (.load .one (.op .add [.var .local (ofString "stable_logs"),.const 0#64]))
                (.seq (.assign .local (ofString "i") (.const 0#64))
                  (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
                      (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
                          .panop .mul [.var .local (ofString "i"),.const 8#64]])
                        (.load .one (.op .add [.var .local (ofString "lp"),
                          .panop .mul [.var .local (ofString "i"),.const 8#64]])))
                        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1#64]))))
                    (.decCall (ofString "rl") .one (ofString "lst_push")
                      [.load .one (.op .add [.var .global (ofString "bo"),.const 72#64]),.const 8#64]
                      (.seq (.store (.var .local (ofString "rl")) (.var .local (ofString "stable_logs"))) rest))))))))))))) := by
  refine aqgd_decD (Qb := fun _ M G => QM M G) (ofString "nl") .one _ (fun h => h.elim)
    (Pb := fun L M G => ∃ Nl : BitVec 64, ((LPSo Y Ix L ∧ L.lookup (ofString "nl") = some (.val (.word Nl))) ∧
      PB n c T Out ko D B Excl Hb Nj M0 M G) ∧ BL W40 Hb L40 8#64 M G ∧ BL W72 Hb L72 8#64 M G) ?_ ?_
    (fun _ _ _ _ _ _ _ h => h)
  · intro F s v _ _ _ _ ⟨⟨lp,pb⟩,bls⟩ _ ev _
    obtain ⟨y,rfl⟩ := isWord_load s _ v ev
    exact ⟨y,⟨⟨lpso_upd lp _ _ (by decide) (by decide),lookup_update_eq' _ _ _⟩,pb⟩,bls⟩
  refine aqgd_exE (fun Nl => ?_)
  refine aqgd_decD (Qb := fun _ M G => QM M G) (ofString "lp") .one _ (fun h => h.elim)
    (Pb := fun L M G => ∃ Lp : BitVec 64, (LDnO Y Ix Nl Lp L ∧ PB n c T Out ko D B Excl Hb Nj M0 M G) ∧
      BL W40 Hb L40 8#64 M G ∧ BL W72 Hb L72 8#64 M G) ?_ ?_ (fun _ _ _ _ _ _ _ h => h)
  · intro F s v _ _ _ _ ⟨⟨⟨lp,hn⟩,pb⟩,bls⟩ _ ev _
    obtain ⟨y,rfl⟩ := isWord_load s _ v ev
    refine ⟨y,⟨⟨lpso_upd lp _ _ (by decide) (by decide),fun p hp => ?_⟩,pb⟩,bls⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl
    · dsimp only; rw [lookup_update_ne' _ _ (by decide)]; exact hn
    · dsimp only; exact lookup_update_eq' _ _ _
  refine aqgd_exE (fun Lp => ?_)
  refine aqgd_seq (aqgd_assignLocal (Q := fun L M G => ∃ Iv N : BitVec 64,
      I1sO Y n c T Out ko D B Excl Hb Nj M0 W40 W72 Ix Nl Lp L40 L72 Iv N L M G) _ _
    (fun s v _ _ ⟨⟨ld,pb⟩,b40,b72⟩ _ ev => ?_)) ?_
  · simp [EV,evalHOLExact] at ev; subst ev
    obtain ⟨N,hN⟩ := bl_cnt b40
    exact ⟨0#64,N,⟨⟨⟨ldn_updO ld _ _ (by decide) (by decide) (by decide) (by decide),lookup_update_eq' _ _ _⟩,
      ⟨Nat.zero_le _,Or.inl rfl⟩⟩,pb⟩,⟨b40,hN⟩,b72⟩
  refine aqgd_seq (loop1O2 bk Ix Nl Lp L40 L72 hW40 hdis hH40 hOut hB40) ?_
  exact aqgd_conseq (P := fun L M G => ((LDnO Y Ix Nl Lp L ∧ PB n c T Out ko D B Excl Hb Nj M0 M G) ∧
      BL W40 Hb L40 8#64 M G ∧ BL W72 Hb L72 8#64 M G) ∧ (Nl.toNat < 2 ^ 63 → 8 * Nl.toNat < 2 ^ 64))
    (aqgd_pureE (fun hbd => ptSufD_capO2 bk Ix Nl Lp L40 L72 hW72 hdis hH40 hH72 hOut hB72 hbd (hrest Nl Lp)))
    (fun L M G ⟨Iv,N,⟨⟨⟨⟨ld,_⟩,_⟩,pb⟩,⟨b40,_⟩,b72⟩,hb⟩ => ⟨⟨⟨ld,pb⟩,b40,b72⟩,hb⟩) (fun _ _ _ h => h)
    (fun _ _ _ h => h)

#print axioms ptSufD_headO2

end l1b
end InitECandidate.Runtime
