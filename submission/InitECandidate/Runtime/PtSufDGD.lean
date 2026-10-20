import InitECandidate.Runtime.PtBlkGD
/-!
Spine drop 126 of the actual `process_transaction` up to the block-list pushes (`nl`, `lp`, the copy of the
transaction logs into the block list `lds(bo + 40)` with `lst_push`, the fresh `stable_logs` list and its copy loop,
and `rl = lst_push(lds(bo + 72), 8); st rl, stable_logs`). The suffix state is `PB` at the heap pointer `Hb` of the
drop; the two block lists have disjoint word sets `W40`, `W72` of block-object words. The log count `nl` is
interpreter data: the first loop's successful pushes bound it by the block-list capacity (below `HEAP_END / 8`),
which bounds the copy into the fresh `stable_logs` buffer.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The signed loop guard on a small left operand. -/
theorem slt_small {a b : BitVec 64} (ha : a.toNat < 2 ^ 63) :
    Compiler.Encoders.Asm.wordCmpHOL .less a b = decide (b.toNat < 2 ^ 63 ∧ a.toNat < b.toNat) := by
  have ha' : a.toNat < 2 ^ (64 - 1) := ha
  simp only [Compiler.Encoders.Asm.wordCmpHOL,Compiler.Encoders.Asm.holAsmSignedLess,if_pos ha']
  by_cases hb : b.toNat < 2 ^ (64 - 1)
  · rw [if_pos hb]; simp only [decide_eq_decide]; exact ⟨fun h => ⟨hb,h⟩,fun h => h.2⟩
  · rw [if_neg hb]; simp only [Bool.false_eq,decide_eq_false_iff_not,not_and]
    exact fun h => absurd h hb

theorem mem_word {M : Mem} (x : BitVec 64) : ∃ y : BitVec 64, M x = .word y := by
  generalize M x = m
  cases m with
  | word y => exact ⟨y,rfl⟩

section st
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc Hb Nj : BitVec 64} {M0 : Mem}

/-- `st name, v` into a slot `S` of the list at `Lh` (`SlotOK`): keeps `PB` and side facts `R` that survive a write
at a slot word among `Wb` off the header or at or above `Hb`. -/
theorem aqgd_store_slot {LP : GA → Prop} {Wb : BitVec 64 → Prop} {R : Mem → GA → Prop} (name : MlS) (v : ExpHOL 64)
    (S Lh E : BitVec 64) (hE1 : 1 ≤ E.toNat) (hWb : ∀ x, Wb x → BW n c Out Excl w x) (hOut : Out w)
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x, EV s v = some x → ∃ y : BitVec 64, x = .val (.word y))
    (hR : ∀ (M M' : Mem) (G : GA), R M G → ((Wb S ∧ ¬ HdW Lh S) ∨ Hb.toNat ≤ S.toNat) →
      (∀ x, x ≠ S → M' x = M x) → R M' G) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => ((LP L ∧ L.lookup name = some (.val (.word S))) ∧ PB n c T Out ko D B Excl Hb Nj M0 M G) ∧
        SlotOK Wb Hb Lh S E G ∧ R M G)
      (fun L M G => LP L ∧ PB n c T Out ko D B Excl Hb Nj M0 M G ∧ R M G) RR
      (.store (.var .local name) v) := by
  refine aqgd_storeD _ _ (fun s G _ _ hG pre _ => ?_) (fun s x _ _ _ _ _ _ ev => hv s x ev)
  unfold GIs at hG; subst hG
  obtain ⟨⟨⟨lp,hS⟩,pb⟩,⟨_,slot⟩,r⟩ := pre
  have hwHb := regT_out_lt pb.2.1 hOut
  have hS0 : (Wb S ∧ ¬ HdW Lh S) ∨ Hb.toNat ≤ S.toNat := by
    rcases slot with inW | ⟨_,_,hb,_⟩
    · exact Or.inl (inW S (le_refl _) (by omega))
    · exact Or.inr hb
  refine ⟨S,by simp [EV,evalHOLExact,hS],fun e => ?_,fun y _ => ?_⟩
  · subst e
    rcases hS0 with ⟨hw,_⟩ | hb
    · exact (hWb _ hw).2.2.2 rfl
    · omega
  refine ⟨lp,?_,hR _ _ _ r hS0 (fun x hx => by simp [hx])⟩
  rcases hS0 with ⟨hw,_⟩ | hb
  · exact pb_wr (fun x => x = S) pb (fun x hx => by subst hx; exact ⟨(hWb _ hw).1,(hWb _ hw).2.1,(hWb _ hw).2.2.1⟩)
      (fun x _ hx => by simp [hx])
  · exact pb_wr (fun _ => False) pb (fun _ h => h.elim) (fun x hx _ => by
      have : x ≠ S := fun e => by subst e; omega
      simp [this])

#print axioms aqgd_store_slot
end st
/-- Suffix locals during the log copies: `LPS`, `nl = Nl`, `lp = Lp`. -/
def LDn (Ix Nl Lp : BitVec 64) (L : GA) : Prop :=
  LPS Ix L ∧ LK [(ofString "nl",Nl),(ofString "lp",Lp)] L

theorem ldn_upd {Ix Nl Lp : BitVec 64} {L : GA} (h : LDn Ix Nl Lp L) (x : MlS) (v : ValueHOL 64)
    (h1 : x ≠ ofString "index") (h2 : x ≠ ofString "sender") (h3 : ofString "nl" ≠ x) (h4 : ofString "lp" ≠ x) :
    LDn Ix Nl Lp (L.update (x,v)) :=
  ⟨lps_upd h.1 x v h1 h2,lk_update h.2 x v (fun p hp => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl <;> assumption)⟩

theorem ldn_res {Ix Nl Lp : BitVec 64} {L : GA} (h : LDn Ix Nl Lp L) (x : MlS) (o : Option (ValueHOL 64))
    (h1 : x ≠ ofString "index") (h2 : x ≠ ofString "sender") (h3 : ofString "nl" ≠ x) (h4 : ofString "lp" ≠ x) :
    LDn Ix Nl Lp (L.resVarEq (x,o)) :=
  ⟨lps_res h.1 x o h1 h2,lk_res h.2 x o (fun p hp => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl <;> assumption)⟩

/-- A write confined to words off the header of `Lh` (and a heap pointer that only grows) keeps `BL`. -/
theorem bl_frame {Wb : BitVec 64 → Prop} {Hb Lh E : BitVec 64} {M M' : Mem} {G G' : GA}
    (h : BL Wb Hb Lh E M G) (keep : ∀ x, HdW Lh x → M' x = M x)
    (hH : ∀ H, HeapIs G H → ∃ H', HeapIs G' H' ∧ H.toNat ≤ H'.toNat) : BL Wb Hb Lh E M' G' := by
  obtain ⟨hW,hLb,P,N,Cp,H,⟨d0,d8,d16⟩,hH0,hNC,hC0,hbuf,alt⟩ := h
  obtain ⟨H',hH',le⟩ := hH H hH0
  exact ⟨hW,hLb,P,N,Cp,H',⟨(keep _ (Or.inl rfl)).trans d0,(keep _ (Or.inr (Or.inl rfl))).trans d8,
    (keep _ (Or.inr (Or.inr rfl))).trans d16⟩,hH',hNC,hC0,by omega,alt⟩

theorem hdw_lt {Lh Hb x : BitVec 64} (hLb : Lh.toNat + 24 ≤ Hb.toNat) (h : HdW Lh x) : x.toNat < Hb.toNat := by
  rcases h with rfl | rfl | rfl
  · omega
  · simp [BitVec.toNat_add]; omega
  · simp [BitVec.toNat_add]; omega

/-- First-loop counters: `i = Iv` is at most the block-list count `N`, and either `0` or at most `Nl < 2^63`. -/
def C1 (Nl Iv N : BitVec 64) : Prop :=
  Iv.toNat ≤ N.toNat ∧ (Iv = 0#64 ∨ (Iv.toNat ≤ Nl.toNat ∧ Nl.toNat < 2 ^ 63))

section l1
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc Hb Nj : BitVec 64} {M0 : Mem} {W40 W72 : BitVec 64 → Prop}

/-- First-loop state at `i = Iv` with block-list count `N`. -/
def I1s (n : Nat) (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (ko : Fin n) (D : BitVec 64 → Prop) (B : Bool)
    (Excl : BitVec 64 → Prop) (Hb Nj : BitVec 64) (M0 : Mem) (W40 W72 : BitVec 64 → Prop)
    (Ix Nl Lp L40 L72 Iv N : BitVec 64) (L : GA) (M : Mem) (G : GA) : Prop :=
  (((LDn Ix Nl Lp L ∧ L.lookup (ofString "i") = some (.val (.word Iv))) ∧ C1 Nl Iv N) ∧
    PB n c T Out ko D B Excl Hb Nj M0 M G) ∧
    (BL W40 Hb L40 8#64 M G ∧ M (L40 + 8#64) = .word N) ∧ BL W72 Hb L72 8#64 M G

/-- The first-loop body: `slot = lst_push(lds(bo + 40), 8); st slot, lds(lp + i * 8); i = i + 1`. -/
theorem loop1Body (Ix Nl Lp L40 L72 Iv N : BitVec 64)
    (hW40 : ∀ x, W40 x → BW n c Out Excl w x)
    (hdis : ∀ x, W40 x → ¬ W72 x) (hH40 : ∀ x, HdW L40 x → W40 x) (hOut : Out w)
    (hB40 : Out (Bo + 40#64) ∧ ¬ Excl (Bo + 40#64) ∧ M0 (Bo + 40#64) = .word L40)
    (hg : Nl.toNat < 2 ^ 63 ∧ Iv.toNat < Nl.toNat) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (I1s n c T Out ko D B Excl Hb Nj M0 W40 W72 Ix Nl Lp L40 L72 Iv N)
      (fun L M G => ∃ Iv' N' : BitVec 64, I1s n c T Out ko D B Excl Hb Nj M0 W40 W72 Ix Nl Lp L40 L72 Iv' N' L M G) RR
      (.decCall (ofString "slot") .one (ofString "lst_push")
        [.load .one (.op .add [.var .global (ofString "bo"),.const 40#64]),.const 8#64]
        (.seq (.store (.var .local (ofString "slot"))
            (.load .one (.op .add [.var .local (ofString "lp"),.panop .mul [.var .local (ofString "i"),.const 8#64]])))
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1#64])))) := by
  refine aqgd_decCall_lstPush_pb (Wb := W40) (R := BL W72 Hb L72 8#64)
    (LP := fun L => (LDn Ix Nl Lp L ∧ L.lookup (ofString "i") = some (.val (.word Iv))) ∧ C1 Nl Iv N)
    (LP' := fun L => (LDn Ix Nl Lp L ∧ L.lookup (ofString "i") = some (.val (.word Iv))) ∧ C1 Nl Iv N)
    (Q := fun L M G => ∃ Iv' N' : BitVec 64, I1s n c T Out ko D B Excl Hb Nj M0 W40 W72 Ix Nl Lp L40 L72 Iv' N' L M G)
    (ofString "slot") 40#64 8#64 L40 N hW40 hOut hB40 (by decide)
    (fun L v ⟨⟨ld,hi⟩,c1⟩ => ⟨⟨ldn_upd ld _ v (by decide) (by decide) (by decide) (by decide),
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
    refine aqgd_seq (aqgd_conseq (aqgd_store_slot (LP := fun L => (LDn Ix Nl Lp L ∧
        L.lookup (ofString "i") = some (.val (.word Iv))) ∧ C1 Nl Iv N) (Wb := W40)
        (R := fun M G => (BL W40 Hb L40 8#64 M G ∧ M (L40 + 8#64) = .word (N + 1#64) ∧ N.toNat + 1 < 2 ^ 64) ∧
          BL W72 Hb L72 8#64 M G) (ofString "slot") _ S L40 8#64 (by decide) hW40 hOut
        (fun s x ev => isWord_load s _ x ev) hR')
      (fun L M G ⟨⟨⟨lp,hS⟩,pb⟩,bl,slot,b72⟩ => ⟨⟨⟨lp,hS⟩,pb⟩,slot,bl,b72⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)) ?_
    refine aqgd_assignLocal _ _ (fun s v _ _ ⟨⟨⟨ld,hi⟩,hc1,_⟩,pb,⟨b40,cnt,nb⟩,b72⟩ _ ev => ?_)
    simp [EV,evalHOLExact,evalListHOLExact,hi,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
    subst ev
    have eI : (Iv + 1#64).toNat = Iv.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    have eN : (N + 1#64).toNat = N.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
    refine ⟨Iv + 1#64,N + 1#64,⟨⟨⟨ldn_upd ld _ _ (by decide) (by decide) (by decide) (by decide),
      lookup_update_eq' _ _ _⟩,⟨by rw [eI,eN]; exact Nat.succ_le_succ hc1,Or.inr ⟨by omega,hg.1⟩⟩⟩,pb⟩,⟨b40,cnt⟩,b72⟩
  · intro L M G L' M' G' _ ⟨Iv',N',⟨⟨⟨ld,hi⟩,c1⟩,pb⟩,b40,b72⟩
    exact ⟨Iv',N',⟨⟨⟨ldn_res ld _ _ (by decide) (by decide) (by decide) (by decide),
      by rw [resVarEq_lookup_ne' _ _ _ _ (by decide)]; exact hi⟩,c1⟩,pb⟩,b40,b72⟩

#print axioms loop1Body

/-- The first-loop counter is small: `Iv ≤ N ≤ cap` with the `8·cap`-byte buffer below the heap pointer. -/
theorem i1_small {Ix Nl Lp L40 L72 Iv N : BitVec 64} {L : GA} {M : Mem} {G : GA}
    (h : I1s n c T Out ko D B Excl Hb Nj M0 W40 W72 Ix Nl Lp L40 L72 Iv N L M G) :
    8 * N.toNat < 2 ^ 64 ∧ Iv.toNat ≤ N.toNat := by
  obtain ⟨⟨⟨_,c1⟩,_⟩,⟨⟨_,_,P,N',Cp,H,hd,_,hNC,_,hbuf,_⟩,cnt⟩,_⟩ := h
  have e := word_inj hd.2.1 cnt
  subst e
  have : H.toNat < 2 ^ 64 := H.isLt
  have e8 : (8#64).toNat = 8 := rfl
  rw [e8] at hbuf
  exact ⟨by omega,c1.1⟩

/-- The first loop `while i < nl { ... }`; on exit a nonnegative `nl` is at most the block-list count. -/
theorem loop1 (Ix Nl Lp L40 L72 : BitVec 64)
    (hW40 : ∀ x, W40 x → BW n c Out Excl w x)
    (hdis : ∀ x, W40 x → ¬ W72 x) (hH40 : ∀ x, HdW L40 x → W40 x) (hOut : Out w)
    (hB40 : Out (Bo + 40#64) ∧ ¬ Excl (Bo + 40#64) ∧ M0 (Bo + 40#64) = .word L40) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => ∃ Iv N : BitVec 64, I1s n c T Out ko D B Excl Hb Nj M0 W40 W72 Ix Nl Lp L40 L72 Iv N L M G)
      (fun L M G => ∃ Iv N : BitVec 64, I1s n c T Out ko D B Excl Hb Nj M0 W40 W72 Ix Nl Lp L40 L72 Iv N L M G ∧
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
    have sm := i1_small hiv
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
    have sm := i1_small hiv
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
      I1s n c T Out ko D B Excl Hb Nj M0 W40 W72 Ix Nl Lp L40 L72 Iv N L M G ∧
        (Nl.toNat < 2 ^ 63 ∧ Iv.toNat < Nl.toNat))
      (aqgd_exE (fun Iv => aqgd_exE (fun N => aqgd_pureE (fun hg =>
        loop1Body Ix Nl Lp L40 L72 Iv N hW40 hdis hH40 hOut hB40 hg))))
      (fun L M G ⟨⟨Iv,N,hiv⟩,hc⟩ => ⟨Iv,N,hiv,hc Iv hiv.1.1.1.2⟩) (fun _ _ _ h => h) (fun _ _ _ h => h))
  · intro L M G h
    rcases h with ⟨⟨Iv,N,hiv⟩,he⟩ | h
    · refine ⟨Iv,N,hiv,fun hnl => ?_⟩
      have sm := i1_small hiv
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

#print axioms loop1
end l1
end InitECandidate.Runtime
