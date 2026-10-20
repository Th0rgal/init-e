import InitECandidate.Runtime.PtLstPushGD
/-!
Block-output lists in the `process_transaction` suffix. `PB` is the suffix state with the registry content fixed at
`Hb` (the heap pointer where the suffix phase starts; every later heap pointer is at least `Hb`). A block list at
`Lh` (`BL`) has its three header words among the block-object words `BW` (outside words in `Excl`, no registry pointer
cell, not the watched word) and its buffer either among `BW` or fresh at or above `Hb`. The actual
`slot = lst_push(lds(bo + k), E)` keeps `PB` and `BL` and returns a slot of `E` bytes that is either among `BW` or
fresh at or above `Hb`, below the current heap pointer.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Suffix state: heap pointer at least `Hb`, the registry with content at `Hb`, the journal counter, and the outside
words outside `Excl` as in `M0`. -/
def PB (n : Nat) (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (ko : Fin n) (D : BitVec 64 → Prop) (B : Bool)
    (Excl : BitVec 64 → Prop) (Hb Nj : BitVec 64) (M0 : Mem) (M : Mem) (G : GA) : Prop :=
  (∃ H : BitVec 64, HeapIs G H ∧ Hb.toNat ≤ H.toNat) ∧ RegT n c T Out Hb M D B ko ∧
    G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∀ x, Out x → ¬ Excl x → M x = M0 x

/-- Block-object words: outside words in `Excl`, no registry pointer cell, not the watched word. -/
def BW (n : Nat) (c : Fin n → BitVec 64) (Out Excl : BitVec 64 → Prop) (w x : BitVec 64) : Prop :=
  Out x ∧ (∀ i, x ≠ c i) ∧ Excl x ∧ x ≠ w

/-- A valid list at `Lh` with element size `E`: header words among `Wb`, buffer among `Wb` or at or above `Hb`, and
below the heap pointer. -/
def BL (Wb : BitVec 64 → Prop) (Hb Lh E : BitVec 64) (M : Mem) (G : GA) : Prop :=
  (∀ x, HdW Lh x → Wb x) ∧ Lh.toNat + 24 ≤ Hb.toNat ∧
    ∃ P N Cp H : BitVec 64, LHd Lh P N Cp M ∧ HeapIs G H ∧ N.toNat ≤ Cp.toNat ∧ 0 < Cp.toNat ∧
      P.toNat + E.toNat * Cp.toNat ≤ H.toNat ∧
      ((∀ x : BitVec 64, P.toNat ≤ x.toNat → x.toNat < P.toNat + E.toNat * Cp.toNat → Wb x ∧ ¬ HdW Lh x) ∨
        Hb.toNat ≤ P.toNat)

/-- An `E`-byte slot at `S` of the list at `Lh`: among `Wb` off the header, or at or above `Hb` and below the heap
pointer. -/
def SlotOK (Wb : BitVec 64 → Prop) (Hb Lh S E : BitVec 64) (G : GA) : Prop :=
  S.toNat + E.toNat < 2 ^ 64 ∧
    ((∀ x : BitVec 64, S.toNat ≤ x.toNat → x.toNat < S.toNat + E.toNat → Wb x ∧ ¬ HdW Lh x) ∨
      ∃ H : BitVec 64, HeapIs G H ∧ Hb.toNat ≤ S.toNat ∧ S.toNat + E.toNat ≤ H.toNat)

theorem slot_arith {N Cn E : Nat} (h : N < Cn) : N * E + E ≤ E * Cn := by
  have := Nat.mul_le_mul_right E h
  rw [Nat.succ_mul] at this
  rw [Nat.mul_comm E Cn]; exact this

theorem word_inj {a b : BitVec 64} {M : Mem} {x : BitVec 64} (h1 : M x = .word a) (h2 : M x = .word b) : a = b := by
  have := h1.symm.trans h2
  simpa using this

section pb
variable {D : BitVec 64 → Prop} {B : Bool}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl : BitVec 64 → Prop} {Hb Nj : BitVec 64} {M0 : Mem}

/-- Changes confined to a set `S` of outside words in `Excl` that are no pointer cell, plus words at or above `Hb`,
keep `PB`. -/
theorem pb_wr {M M' : Mem} {G : GA} (S : BitVec 64 → Prop) (h : PB n c T Out ko D B Excl Hb Nj M0 M G)
    (hS : ∀ x, S x → Out x ∧ (∀ i, x ≠ c i) ∧ Excl x)
    (keep : ∀ x, x.toNat < Hb.toNat → ¬ S x → M' x = M x) : PB n c T Out ko D B Excl Hb Nj M0 M' G := by
  classical
  obtain ⟨hh,reg,hn,fr⟩ := h
  let M2 : Mem := fun x => if S x then M' x else M x
  have r2 : RegT n c T Out Hb M2 D B ko :=
    regT_frame reg S (fun x hx => ⟨(hS x hx).1,(hS x hx).2.1⟩) (fun x hx => by simp [M2,hx])
  refine ⟨hh,regT_below r2 (fun x hx => ?_),hn,fun x ho hx => ?_⟩
  · by_cases hs : S x
    · simp [M2,hs]
    · simp only [M2,hs,if_false]; exact keep x hx hs
  · have hs : ¬ S x := fun hs => hx (hS x hs).2.2
    exact (keep x (regT_out_lt reg ho) hs).trans (fr x ho hx)

theorem pb_glob {M : Mem} {G G' : GA} (h : PB n c T Out ko D B Excl Hb Nj M0 M G)
    (hH : ∃ H : BitVec 64, HeapIs G' H ∧ Hb.toNat ≤ H.toNat)
    (hn : G'.lookup (ofString "journal_n") = some (.val (.word Nj))) : PB n c T Out ko D B Excl Hb Nj M0 M G' :=
  ⟨hH,h.2.1,hn,h.2.2.2⟩

theorem pb_excl {M : Mem} {G : GA} {Excl' : BitVec 64 → Prop} (h : PB n c T Out ko D B Excl Hb Nj M0 M G)
    (sub : ∀ x, Excl x → Excl' x) : PB n c T Out ko D B Excl' Hb Nj M0 M G :=
  ⟨h.1,h.2.1,h.2.2.1,fun x ho hx => h.2.2.2 x ho (fun e => hx (sub x e))⟩

theorem pb_of_pxr {H0 : BitVec 64} {M : Mem} {G : GA} (h : PXR n c T Out ko D B Excl H0 M0 M G) :
    ∃ Hb Nj : BitVec 64, HeapIs G Hb ∧ H0.toNat ≤ Hb.toNat ∧ PB n c T Out ko D B Excl Hb Nj M0 M G := by
  obtain ⟨H,Nj,hH,le,reg,hn,fr⟩ := h
  exact ⟨H,Nj,hH,le,⟨⟨H,hH,le_refl _⟩,reg,hn,fr⟩⟩

theorem pxr_of_pb {H0 : BitVec 64} {M : Mem} {G : GA} (h0 : H0.toNat ≤ Hb.toNat)
    (h : PB n c T Out ko D B Excl Hb Nj M0 M G) : PXR n c T Out ko D B Excl H0 M0 M G := by
  obtain ⟨⟨H,hH,le⟩,reg,hn,fr⟩ := h
  exact ⟨H,Nj,hH,by omega,regT_mono reg le,hn,fr⟩

#print axioms pb_wr
end pb

section ls
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc Hb Nj : BitVec 64} {M0 : Mem}

/-- `name = lst_push(lds(bo + k), E)` on the block list `Lh = M0 (bo + k)` (count `Nc`); the other memory facts `R`
are framed by the header words and the words at or above the heap pointer. -/
theorem aqgd_decCall_lstPush_pb {LP LP' : GA → Prop} {Q Q2 : GA → Mem → GA → Prop} {Wb : BitVec 64 → Prop}
    {R : Mem → GA → Prop} (name : MlS) (k E Lh Nc : BitVec 64)
    {cont : ProgHOL 64} (hWb : ∀ x, Wb x → BW n c Out Excl w x)
    (hOut : Out w) (hBk : Out (Bo + k) ∧ ¬ Excl (Bo + k) ∧ M0 (Bo + k) = .word Lh)
    (hE1 : 1 ≤ E.toNat) (hup : ∀ L v, LP L → LP' (L.update (name,v)))
    (hR : ∀ (M M' : Mem) (G G' : GA) (H H' : BitVec 64), R M G → HeapIs G H → Hb.toNat ≤ H.toNat → HeapIs G' H' →
      H.toNat ≤ H'.toNat →
      (∀ x, x.toNat < H.toNat → ¬ HdW Lh x → M' x = M x) → R M' G')
    (hcont : ∀ S : BitVec 64, AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => ((LP' L ∧ L.lookup name = some (.val (.word S))) ∧ PB n c T Out ko D B Excl Hb Nj M0 M G) ∧
        (BL Wb Hb Lh E M G ∧ M (Lh + 8#64) = .word (Nc + 1#64) ∧ Nc.toNat + 1 < 2 ^ 64) ∧
        SlotOK Wb Hb Lh S E G ∧ R M G) Q RR cont)
    (hres : ∀ L M G L' M' G', (LP L ∧ PB n c T Out ko D B Excl Hb Nj M0 M G) ∧
      (BL Wb Hb Lh E M G ∧ M (Lh + 8#64) = .word Nc) ∧ R M G →
      Q L' M' G' → Q2 (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => (LP L ∧ PB n c T Out ko D B Excl Hb Nj M0 M G) ∧ (BL Wb Hb Lh E M G ∧ M (Lh + 8#64) = .word Nc) ∧
        R M G) Q2 RR
      (.decCall name .one (ofString "lst_push") [.load .one (.op .add [.var .global (ofString "bo"),.const k]),.const E]
        cont) := by
  refine aqgd_decCallSpecS (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (LK [(ofString "l",Lh),(ofString "esz",E)] L ∧ M = M0' ∧ G = G0') ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ((∃ P N Cp : BitVec 64, LHd Lh P N Cp M0' ∧ LPPost Lh E P N Cp (hpOf G0') M0' G0' v M' G') ∧ ScrIs Sc G') ∧
        G'.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (Pc := fun L M G => ∃ S : BitVec 64, (((LP' L ∧ L.lookup name = some (.val (.word S))) ∧
      PB n c T Out ko D B Excl Hb Nj M0 M G) ∧
      (BL Wb Hb Lh E M G ∧ M (Lh + 8#64) = .word (Nc + 1#64) ∧ Nc.toNat + 1 < 2 ^ 64) ∧
      SlotOK Wb Hb Lh S E G ∧ R M G) ∧ True)
    (Qc := Q) _ _ _ _ _ _ _ originalRuntimeCode_lstPush_lookup
    (fun values callee rs h => callee_entry_sl _ values _ _ _ originalRuntimeCode_lstPush_lookup (by simp) _ callee rs h)
    ?_ ?_ (fun h => h.elim) ?_ (aqgd_exE (fun S => aqgd_pureE (fun _ => hcont S))) hres
  · intro L0 M0' G0' ⟨⟨_,pb⟩,⟨⟨hW,hLb,P,N,Cp,H1,hd,hH1,hNC,hC0,hbuf,_⟩,_⟩,_⟩
    obtain ⟨⟨H,hH,hbH⟩,reg,hn,_⟩ := pb
    have e1 := heapIs_unique hH hH1
    subst e1
    rw [hpOf_eq hH]
    have hwH := regT_out_lt reg hOut
    have hwh : ¬ HdW Lh w := fun h => (hWb w (hW w h)).2.2.2 rfl
    refine aqgd_of_arenaFact (Φ := ScrIs Sc G0' ∧ H.toNat ≤ 33806089496)
      (fun _ _ g aw ⟨⟨_,_,hg⟩,_⟩ => by subst hg; exact ⟨aw.2,(jws_heap_facts aw.1.1.1 hH).2.1⟩) ?_
    intro ⟨hsc,hHE⟩
    have hsz : E.toNat * Cp.toNat * 2 < 2 ^ 64 := by omega
    refine aqgd_conseq (P := fun L M G => (((LK [(ofString "l",Lh),(ofString "esz",E)] L ∧ M = M0' ∧
        HeapIs G H) ∧ G = G0') ∧ ScrIs Sc G) ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj))) ?_
      (fun L M G h => by obtain ⟨⟨lk,hM,hG⟩,jn⟩ := h; subst hG; exact ⟨⟨⟨⟨lk,hM,hH⟩,rfl⟩,hsc⟩,jn⟩)
      (fun _ _ _ h => h) (fun _ _ _ h => h)
    refine aqgd_conseq (aqgd_jwsbus_of_jwsn (U := U) (Bo := Bo)
      (keepsBo_of_installed originalRuntimeCode_lstPush_lookup (by decide))
      (keepsWs_of_installed originalRuntimeCode_lstPush_lookup (by decide))
      (P := fun L M G => ((LK [(ofString "l",Lh),(ofString "esz",E)] L ∧ M = M0' ∧ HeapIs G H) ∧ G = G0') ∧
        ScrIs Sc G) (Nj := Nj)
      (aqgd_conseq (aqgd_keepScr (Sc := Sc) (keepsScr_of_installed originalRuntimeCode_lstPush_lookup (by decide))
        (lstPush_spec (D := D) (B := B) (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C) (SKB := SKB)
          (Nj := Nj) (w := w) Lh E P N Cp H M0' G0' (by omega) (by omega) hwh hd hNC hC0 hE1 (by omega) hsz))
        (fun _ _ _ h => h) (fun _ _ _ h => h.1.elim) (fun _ _ _ h => h)))
      (fun _ _ _ h => h) (fun _ _ _ h => h.elim) ?_
    intro v M' G' ⟨⟨post,sc⟩,hn'⟩
    exact ⟨⟨⟨P,N,Cp,hd,post⟩,sc⟩,hn'⟩
  · intro F s values callee rs aw G hG ⟨⟨_,pb⟩,_,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨v1,vs,rfl,ev1,r1⟩ := evalList_cons' s _ _ _ args
    obtain ⟨v2,vs2,rfl,ev2,r2⟩ := evalList_cons' s _ _ _ r1
    have := evalList_nil' s _ r2; subst this
    have e1 := ev_load_goff s _ Bo k v1 aw.1.1.2 ev1
    rw [pb.2.2.2 _ hBk.1 hBk.2.1,hBk.2.2] at e1
    subst e1
    simp [EV,evalHOLExact] at ev2; subst ev2
    have e := callee_eq originalRuntimeCode_lstPush_lookup lookup
    refine ⟨⟨fun p hp => ?_,rfl,rfl⟩,pb.2.2.1⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl <;> (rw [e]; simp (config := {decide := true}))
  · intro L M G v M' G' ⟨⟨lp,pb⟩,⟨⟨hW,hLb,P0',N0,Cp0,H0',hd0,hH0,_,_,hbuf0,alt0⟩,hNc⟩,r⟩
      ⟨⟨⟨P,N,Cp,hd,post⟩,_⟩,hn'⟩ _
    obtain ⟨H,hH,hbH⟩ := pb.1
    have eH := heapIs_unique hH hH0
    subst eH
    rw [hpOf_eq hH] at post
    obtain ⟨fr,_,Pn,Cn,Hc,ev,hd',hHc,le,lt,hbuf',alt⟩ := post
    subst ev
    have eP := word_inj hd.1 hd0.1
    have eC := word_inj hd.2.2 hd0.2.2
    have eN := word_inj hd.2.1 hNc
    subst eP eC eN
    have hHc64 : Hc.toNat < 2 ^ 64 := Hc.isLt
    have sa := slot_arith (E := E.toNat) lt
    have eNE : (N * E).toNat = N.toNat * E.toNat := mul_nat (by omega)
    have eS : (Pn + N * E).toNat = Pn.toNat + N.toNat * E.toNat := by
      rw [BitVec.toNat_add,eNE]; exact Nat.mod_eq_of_lt (by omega)
    have eN1 : (N + 1#64).toNat = N.toNat + 1 := by
      rw [BitVec.toNat_add]; simp; omega
    refine ⟨Pn + N * E,⟨⟨⟨hup L _ lp,lookup_update_eq' _ _ _⟩,pb_glob (pb_wr (HdW Lh) pb
      (fun x hx => let b := hWb x (hW x hx); ⟨b.1,b.2.1,b.2.2.1⟩) (fun x hx hn => fr x (by omega) hn))
        ⟨Hc,hHc,by omega⟩ hn'⟩,
      ⟨⟨hW,hLb,Pn,N + 1#64,Cn,Hc,hd',hHc,by omega,by omega,hbuf',?_⟩,hd'.2.1,by omega⟩,⟨by omega,?_⟩,
      hR M M' G G' H Hc r hH hbH hHc le fr⟩,trivial⟩
    · rcases alt with ⟨rfl,rfl⟩ | ⟨hp,_⟩
      · exact alt0
      · exact Or.inr (by omega)
    · rcases alt with ⟨rfl,rfl⟩ | ⟨hp,_⟩
      · rcases alt0 with inW | hp
        · exact Or.inl (fun x lo hi => inW x (by omega) (by omega))
        · exact Or.inr ⟨Hc,hHc,by omega,by omega⟩
      · exact Or.inr ⟨Hc,hHc,by omega,by omega⟩

#print axioms aqgd_decCall_lstPush_pb

end ls
end InitECandidate.Runtime
