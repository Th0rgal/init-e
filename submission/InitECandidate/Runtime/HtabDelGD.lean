import InitECandidate.Runtime.HtabDelFine
import InitECandidate.Runtime.TableContent
import InitECandidate.Runtime.ArenaHeapGDLoop
/-!
All-outcome watched-word frame of the original `htab_del` body in the fixed-domain triple `AQGD`, proved directly
over the actual source with a content loop invariant (`DMI`: occupancy bytes fixed from entry, occupied order
positions < capacity, live order entries < capacity, header kept). Every store of the body (key memcpy window, value,
order, order-position, occupancy byte, count) lies in the table's header or one of its five arrays (`InTabF`), so a
word outside them is unchanged in every outcome (normal, returned, error, timeout). `del_aqgd_content` adds the
returned-run content invariant (`TCont` with count kept or decremented) by replaying the checked aligned-world
contract `htabDel_returned_fine` with a larger clock.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Content facts kept through the `htab_del` backward-shift loop (occupancy `occ` fixed from entry). -/
def DMI (occ : BitVec 64 → Option UInt8) (M0 : Mem) (T KL SD C N KS VS US OS OPS : BitVec 64) (M : Mem) : Prop :=
  (∀ q : BitVec 64, q.toNat < C.toNat → M (panByteAlignHOL (US + q)) = M0 (panByteAlignHOL (US + q))) ∧
  (∀ q : BitVec 64, q.toNat < C.toNat → occ q ≠ some 0 →
    ∃ x : BitVec 64, M (OPS + q * 8) = .word x ∧ x.toNat < C.toNat) ∧
  (∀ p : BitVec 64, p.toNat < N.toNat → ∃ x : BitVec 64, M (OS + p * 8) = .word x ∧ x.toNat < C.toNat) ∧
  Hdr M T KL SD C N KS VS US OS OPS

/-- Region facts of an aligned table used by the loop invariant. -/
structure DReg (T KL SD C KS VS US OS OPS : BitVec 64) (b : Nat) : Prop where
  pow : C.toNat = 2 ^ b
  hk : T.toNat + 72 ≤ KS.toNat
  hv : T.toNat + 72 ≤ VS.toNat
  kb : KS.toNat + C.toNat * SD.toNat ≤ US.toNat
  vb : VS.toNat + C.toNat * 8 ≤ US.toNat
  ub : US.toNat + C.toNat ≤ OS.toNat
  ob : OS.toNat + C.toNat * 8 ≤ OPS.toNat
  eb : OPS.toNat + C.toNat * 8 ≤ 33806089496
  ua : US.toNat % 8 = 0
  fits : KL.toNat ≤ SD.toNat
  sa : SD.toNat % 8 = 0
  ka : KS.toNat % 8 = 0

theorem dreg_of_aligned {F : Type} {s : PanSemStateFiniteExact 64 F}
    {KL T KS SD C US VS OS OPS N : BitVec 64} {b : Nat} (inv : HtabAligned KL T KS SD C US VS OS OPS N b s) :
    DReg T KL SD C KS VS US OS OPS b :=
  ⟨inv.power,inv.headerKeys,inv.headerValues,inv.keysBefore,inv.valuesBefore,inv.usedBefore,inv.orderBefore,
    inv.endBound,inv.usedAligned,inv.fits,inv.strideAligned,inv.keysAligned⟩

theorem byteAlign_lt {US q : BitVec 64} {C : BitVec 64} (ua : US.toNat % 8 = 0) (fit : US.toNat + C.toNat < 2 ^ 64)
    (hq : q.toNat < C.toNat) :
    US.toNat ≤ (panByteAlignHOL (US + q)).toNat ∧ (panByteAlignHOL (US + q)).toNat < US.toNat + C.toNat := by
  rw [byteAlign_toNat,BitVec.toNat_add_of_lt (by omega)]
  constructor
  · have := Nat.div_mul_le_self (US.toNat + q.toNat) 8
    have h2 : US.toNat ≤ (US.toNat + q.toNat) / 8 * 8 := by
      have : US.toNat = US.toNat / 8 * 8 := by omega
      rw [this]
      exact Nat.mul_le_mul_right 8 (Nat.div_le_div_right (by omega))
    omega
  · have := Nat.div_mul_le_self (US.toNat + q.toNat) 8; omega

theorem add_mul8_toNat (base q C : BitVec 64) (hq : q.toNat < C.toNat)
    (fit : base.toNat + C.toNat * 8 ≤ 33806089496) : (base + q * 8).toNat = base.toNat + q.toNat * 8 := by
  have hm : (q * 8).toNat = q.toNat * 8 := by
    rw [BitVec.toNat_mul]; exact Nat.mod_eq_of_lt (by simp; omega)
  rw [BitVec.toNat_add_of_lt (by rw [hm]; omega),hm]

/-- A word write outside the used, order and order-position arrays and the header keeps the loop facts. -/
theorem dmi_write {occ : BitVec 64 → Option UInt8} {M0 M : Mem} {T KL SD C N KS VS US OS OPS : BitVec 64} {b : Nat}
    (rg : DReg T KL SD C KS VS US OS OPS b) (nC : N.toNat ≤ C.toNat) (h : DMI occ M0 T KL SD C N KS VS US OS OPS M)
    (a : BitVec 64) (lo : T.toNat + 72 ≤ a.toNat) (hi : a.toNat < US.toNat) (M' : Mem)
    (hM' : ∀ x, x ≠ a → M' x = M x) :
    DMI occ M0 T KL SD C N KS VS US OS OPS M' := by
  obtain ⟨hu,hp,he,hh⟩ := h
  have fitT : T.toNat + 72 < 2 ^ 64 := by have := rg.eb; have := rg.hk; have := rg.kb; have := rg.ub; omega
  refine ⟨fun q hq => ?_,fun q hq ho => ?_,fun p hp' => ?_,
    hdr_keep hh fitT (fun x lo' hi' => hM' x (fun e => by subst e; omega))⟩
  · have := byteAlign_lt (C := C) rg.ua (by have := rg.eb; have := rg.ob; have := rg.ub; omega) hq
    rw [hM' _ (fun e => by rw [e] at this; omega)]; exact hu q hq
  · obtain ⟨x,hx,xl⟩ := hp q hq ho
    have e := add_mul8_toNat OPS q C hq rg.eb
    exact ⟨x,by rw [hM' _ (fun h => by rw [h] at e; have := rg.ob; have := rg.ub; omega)]; exact hx,xl⟩
  · obtain ⟨x,hx,xl⟩ := he p hp'
    have e := add_mul8_toNat OS p C (by omega) (by have := rg.ob; have := rg.eb; omega)
    exact ⟨x,by rw [hM' _ (fun h => by rw [h] at e; have := rg.ub; omega)]; exact hx,xl⟩

#print axioms dmi_write

/-- Region form: memory kept below the arrays' start and from the used array on keeps the loop facts. -/
theorem dmi_low {occ : BitVec 64 → Option UInt8} {M0 M : Mem} {T KL SD C N KS VS US OS OPS : BitVec 64} {b : Nat}
    (rg : DReg T KL SD C KS VS US OS OPS b) (nC : N.toNat ≤ C.toNat) (h : DMI occ M0 T KL SD C N KS VS US OS OPS M)
    (M' : Mem) (hM' : ∀ x : BitVec 64, (x.toNat < T.toNat + 72 ∨ US.toNat ≤ x.toNat) → M' x = M x) :
    DMI occ M0 T KL SD C N KS VS US OS OPS M' := by
  obtain ⟨hu,hp,he,hh⟩ := h
  have fitT : T.toNat + 72 < 2 ^ 64 := by have := rg.eb; have := rg.hk; have := rg.kb; have := rg.ub; omega
  refine ⟨fun q hq => ?_,fun q hq ho => ?_,fun p hp' => ?_,
    hdr_keep hh fitT (fun x lo' hi' => hM' x (Or.inl hi'))⟩
  · have := byteAlign_lt (C := C) rg.ua (by have := rg.eb; have := rg.ob; have := rg.ub; omega) hq
    rw [hM' _ (Or.inr this.1)]; exact hu q hq
  · obtain ⟨x,hx,xl⟩ := hp q hq ho
    have e := add_mul8_toNat OPS q C hq rg.eb
    exact ⟨x,by rw [hM' _ (Or.inr (by rw [e]; have := rg.ob; have := rg.ub; omega))]; exact hx,xl⟩
  · obtain ⟨x,hx,xl⟩ := he p hp'
    have e := add_mul8_toNat OS p C (by omega) (by have := rg.ob; have := rg.eb; omega)
    exact ⟨x,by rw [hM' _ (Or.inr (by rw [e]; have := rg.ub; omega))]; exact hx,xl⟩

/-- Writing a bounded slot into the order array keeps the loop facts. -/
theorem dmi_write_order {occ : BitVec 64 → Option UInt8} {M0 M : Mem} {T KL SD C N KS VS US OS OPS : BitVec 64}
    {b : Nat} (rg : DReg T KL SD C KS VS US OS OPS b) (nC : N.toNat ≤ C.toNat)
    (h : DMI occ M0 T KL SD C N KS VS US OS OPS M) (x i : BitVec 64) (hx : x.toNat < C.toNat) (hi : i.toNat < C.toNat) :
    DMI occ M0 T KL SD C N KS VS US OS OPS (fun y => if y = OS + x * 8 then .word i else M y) := by
  obtain ⟨hu,hp,he,hh⟩ := h
  have ea := add_mul8_toNat OS x C hx (by have := rg.ob; have := rg.eb; omega)
  have hk := rg.hk; have kb := rg.kb; have ub := rg.ub; have ob := rg.ob; have eb := rg.eb
  have fitT : T.toNat + 72 < 2 ^ 64 := by omega
  refine ⟨fun q hq => ?_,fun q hq ho => ?_,fun p hp' => ?_,
    hdr_keep hh fitT (fun y lo' hi' => word_update_keep y (fun e => by rw [e,ea] at hi'; omega))⟩
  · have := byteAlign_lt (C := C) rg.ua (by omega) hq
    rw [word_update_keep _ (fun e => by rw [e,ea] at this; omega)]; exact hu q hq
  · obtain ⟨y,hy,yl⟩ := hp q hq ho
    have e := add_mul8_toNat OPS q C hq rg.eb
    exact ⟨y,by rw [word_update_keep _ (fun h => by rw [h,ea] at e; omega)]; exact hy,yl⟩
  · by_cases same : OS + p * 8 = OS + x * 8
    · exact ⟨i,by show (if OS + p * 8 = OS + x * 8 then HolWordLab.word i else M (OS + p * 8)) = _; rw [if_pos same],hi⟩
    · obtain ⟨y,hy,yl⟩ := he p hp'
      exact ⟨y,by rw [word_update_keep _ same]; exact hy,yl⟩

/-- Writing a bounded position into the order-position array keeps the loop facts. -/
theorem dmi_write_opos {occ : BitVec 64 → Option UInt8} {M0 M : Mem} {T KL SD C N KS VS US OS OPS : BitVec 64}
    {b : Nat} (rg : DReg T KL SD C KS VS US OS OPS b) (nC : N.toNat ≤ C.toNat)
    (h : DMI occ M0 T KL SD C N KS VS US OS OPS M) (i x : BitVec 64) (hi : i.toNat < C.toNat) (hx : x.toNat < C.toNat) :
    DMI occ M0 T KL SD C N KS VS US OS OPS (fun y => if y = OPS + i * 8 then .word x else M y) := by
  obtain ⟨hu,hp,he,hh⟩ := h
  have ea := add_mul8_toNat OPS i C hi rg.eb
  have hk := rg.hk; have kb := rg.kb; have ub := rg.ub; have ob := rg.ob; have eb := rg.eb
  have fitT : T.toNat + 72 < 2 ^ 64 := by omega
  refine ⟨fun q hq => ?_,fun q hq ho => ?_,fun p hp' => ?_,
    hdr_keep hh fitT (fun y lo' hi' => word_update_keep y (fun e => by rw [e,ea] at hi'; omega))⟩
  · have := byteAlign_lt (C := C) rg.ua (by omega) hq
    rw [word_update_keep _ (fun e => by rw [e,ea] at this; omega)]; exact hu q hq
  · by_cases same : OPS + q * 8 = OPS + i * 8
    · exact ⟨x,by show (if OPS + q * 8 = OPS + i * 8 then HolWordLab.word x else M (OPS + q * 8)) = _; rw [if_pos same],hx⟩
    · obtain ⟨y,hy,yl⟩ := hp q hq ho
      exact ⟨y,by rw [word_update_keep _ same]; exact hy,yl⟩
  · obtain ⟨y,hy,yl⟩ := he p hp'
    have e := add_mul8_toNat OS p C (by omega) (by omega)
    exact ⟨y,by rw [word_update_keep _ (fun h => by rw [h,ea] at e; omega)]; exact hy,yl⟩

#print axioms dmi_write_order
#print axioms dmi_write_opos

variable {D : BitVec 64 → Prop} {B : Bool} {A : HolFiniteMapExact MlS (ValueHOL 64) → Prop} {w : BitVec 64}
  {Vn : MlS → Prop} {RR : ValueHOL 64 → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop}

/-- Occupancy byte read from memory `M` with domain `D` and endianness `B`. -/
noncomputable def occM (D : BitVec 64 → Prop) (B : Bool) (M : Mem) (US q : BitVec 64) : Option UInt8 :=
  @panMemLoadByteHOL 64 _ M D (fun a => Classical.propDecidable (D a)) B (US + q)

theorem occM_eq {F : Type} (s : PanSemStateFiniteExact 64 F) (US q : BitVec 64) :
    hashOccupancyRead s US q = occM s.memaddrs s.be s.memory US q := rfl

/-- Adding a returned-run fact to a fixed-domain triple's return postcondition. -/
theorem aqgd_augment {P Q : GA → Mem → GA → Prop} {X : ValueHOL 64 → Mem → GA → Prop} {p : ProgHOL 64}
    (h : AQGD D B A w Vn P Q RR p)
    (hx : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → DomD D B s →
      P s.locals s.memory s.globals → ∀ v post, evaluateHOLFiniteState s p = (some (.returned v),post) →
      X v post.memory post.globals) :
    AQGD D B A w Vn P Q (fun v M G => RR v M G ∧ X v M G) p := by
  intro F s code dom aw sl G hG pre
  obtain ⟨m,a,n,r,c,b⟩ := h F s code dom aw sl G hG pre
  refine ⟨m,a,n,fun v e => ?_,c,b⟩
  obtain ⟨G',hG',rr⟩ := r v e
  unfold GIs at hG hG'
  subst hG
  exact ⟨G',hG',rr,by rw [← hG']; exact hx s code dom pre v _ (Prod.ext e rfl)⟩

/-- A header-word declaration `name = lds (t + off)`. -/
theorem aqgd_hdrDec {Rm : Mem → Prop} {pairs : List (MlS × BitVec 64)} {T : BitVec 64} (name : MlS) (off val : BitVec 64)
    {Qb Q : GA → Mem → GA → Prop} {body : ProgHOL 64} (hname : ∀ p ∈ pairs, p.1 ≠ name)
    (ht : (ofString "t",T) ∈ pairs) (hval : ∀ M, Rm M → M (T + off) = .word val)
    (hb : AQGD D B A w (fun _ => True) (fun L M G => LK ((name,val) :: pairs) L ∧ Rm M) Qb RR body)
    (hq : ∀ L M (G : GA) L' M' G', LK pairs L ∧ Rm M → Qb L' M' G' → Q (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B A w (fun _ => True) (fun L M G => LK pairs L ∧ Rm M) Q RR
      (.dec name .one (.load .one (.op .add [.var .local (ofString "t"),.const off])) body) :=
  aqgd_dec name .one _ (fun _ => rfl)
    (fun s v H _ _ ⟨hl,hm⟩ _ ev _ => by
      rw [ev_load_off s _ T off v (lk_get hl _ _ ht) ev,hval _ hm]
      exact ⟨lk_cons hl _ _ hname,hm⟩)
    hb hq

#print axioms aqgd_augment

theorem ev_load_at {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) (a : BitVec 64)
    (he : EV s e = some (.val (.word a))) (v : ValueHOL 64) (ev : EV s (.load .one e) = some v) :
    v = .val (s.memory a) := by
  simp only [EV,evalHOLExact] at ev he
  rw [he] at ev
  simp [memLoadHOLExact] at ev
  exact ev.2.symm

/-- Window frame of a body in the fixed-domain triple. -/
theorem aqgd_of_window {Pe : GA → Mem → Prop} {body : ProgHOL 64}
    (hg : OriginalGlobalsFrame body) (nb : noTopBreak body = true) (nc : noTopContinue body = true)
    (Win : BitVec 64 → Prop)
    (hwin : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → Pe s.locals s.memory →
      ∀ x, ¬ Win x → (evaluateHOLFiniteState s body).2.memory x = s.memory x)
    (hw : ¬ Win w) (M0 : Mem) (G0 : GA) :
    AQGD D B A w (fun _ => False) (fun L M G => Pe L M ∧ M = M0 ∧ G = G0) (fun _ _ _ => True)
      (fun _ M' G' => G' = G0 ∧ ∀ x, ¬ Win x → M' x = M0 x) body := by
  intro F s code dom aw sl G hG ⟨pe,hm,hg0⟩
  unfold GIs at hG
  subst hm hG hg0
  refine ⟨hwin s code pe w hw,fun _ => by rw [hg s code]; exact aw,fun _ => ⟨fun _ h => h.elim,_,rfl,trivial⟩,
    fun v _ => ⟨_,rfl,hg s code,hwin s code pe⟩,evaluate_noTopContinue body nc s,evaluate_noTopBreak body nb s⟩

/-- After the occupancy byte store the loop facts hold with the new memory as reference and no occupied slot. -/
theorem dmi_reset {occ : BitVec 64 → Option UInt8} {M0 M : Mem} {T KL SD C N KS VS US OS OPS : BitVec 64} {b : Nat}
    (rg : DReg T KL SD C KS VS US OS OPS b) (nC : N.toNat ≤ C.toNat) (h : DMI occ M0 T KL SD C N KS VS US OS OPS M)
    (a : BitVec 64) (lo : US.toNat ≤ a.toNat) (hi : a.toNat < US.toNat + C.toNat) (M' : Mem)
    (hM' : ∀ x, x ≠ a → M' x = M x) :
    DMI (fun _ => some 0) M' T KL SD C N KS VS US OS OPS M' := by
  obtain ⟨_,_,he,hh⟩ := h
  have hk := rg.hk; have kb := rg.kb; have ub := rg.ub; have ob := rg.ob; have eb := rg.eb
  have fitT : T.toNat + 72 < 2 ^ 64 := by omega
  refine ⟨fun _ _ => rfl,fun _ _ ho => absurd rfl ho,fun p hp' => ?_,
    hdr_keep hh fitT (fun x lo' hi' => hM' x (fun e => by subst e; omega))⟩
  obtain ⟨x,hx,xl⟩ := he p hp'
  have e := add_mul8_toNat OS p C (by omega) (by omega)
  exact ⟨x,by rw [hM' _ (fun h => by rw [h] at e; omega)]; exact hx,xl⟩

#print axioms ev_load_at
#print axioms aqgd_of_window
#print axioms dmi_reset

/-- Base locals of `htab_del` after its header declarations. -/
def dB (T Kk C KL SD KS VS US OS OPS DP : BitVec 64) : List (MlS × BitVec 64) :=
  [(ofString "deleted_pos",DP),(ofString "order_pos",OPS),(ofString "order",OS),(ofString "used",US),
   (ofString "vals",VS),(ofString "keys",KS),(ofString "stride",SD),(ofString "klen",KL),(ofString "cap",C),
   (ofString "key",Kk),(ofString "t",T)]

/-- Loop locals: the cursors `j`, `i` and the base locals. -/
def dL (T Kk C KL SD KS VS US OS OPS DP I J : BitVec 64) : List (MlS × BitVec 64) :=
  (ofString "j",J) :: (ofString "i",I) :: dB T Kk C KL SD KS VS US OS OPS DP

def dNames : List MlS :=
  [ofString "j",ofString "i",ofString "deleted_pos",ofString "order_pos",ofString "order",ofString "used",
   ofString "vals",ofString "keys",ofString "stride",ofString "klen",ofString "cap",ofString "key",ofString "t"]

theorem dL_fresh {x : MlS} (hx : x ∉ dNames) (T Kk C KL SD KS VS US OS OPS DP I J : BitVec 64) :
    ∀ p ∈ dL T Kk C KL SD KS VS US OS OPS DP I J, p.1 ≠ x := by
  intro p hp e
  apply hx
  subst e
  simp only [dL,dB,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h <;> (subst h; simp [dNames])

theorem dB_ne_i (T Kk C KL SD KS VS US OS OPS DP : BitVec 64) :
    ∀ p ∈ dB T Kk C KL SD KS VS US OS OPS DP, p.1 ≠ ofString "i" := by unfold dB; lkne

theorem dB_ne_j (T Kk C KL SD KS VS US OS OPS DP : BitVec 64) :
    ∀ p ∈ dB T Kk C KL SD KS VS US OS OPS DP, p.1 ≠ ofString "j" := by unfold dB; lkne

theorem lk_tail {x : MlS × BitVec 64} {pairs : List (MlS × BitVec 64)} {L : GA} (h : LK (x :: pairs) L) : LK pairs L :=
  fun p hp => h p (List.mem_cons_of_mem _ hp)

/-- `i := j` on the loop locals. -/
theorem lk_set_i {T Kk C KL SD KS VS US OS OPS DP I J : BitVec 64} {L : GA}
    (h : LK (dL T Kk C KL SD KS VS US OS OPS DP I J) L) (I' : BitVec 64) :
    LK (dL T Kk C KL SD KS VS US OS OPS DP I' J) (L.update (ofString "i",.val (.word I'))) := by
  intro p hp
  simp only [dL,List.mem_cons] at hp
  rcases hp with rfl | rfl | hp
  · simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
    exact h (ofString "j",J) (by simp [dL])
  · simp [HolFiniteMapExact.lookup_update,FUPDATE]
  · rw [lk_update (lk_tail (lk_tail h)) _ _ (dB_ne_i _ _ _ _ _ _ _ _ _ _ _) p hp]

/-- Backward-shift loop invariant (occupancy fixed from the entry memory `M0`). -/
def DLI (D : BitVec 64 → Prop) (B : Bool) (M0 : Mem) (T Kk KL SD C N KS VS US OS OPS DP : BitVec 64)
    (L : GA) (M : Mem) (_ : GA) : Prop :=
  ∃ I J : BitVec 64, LK (dL T Kk C KL SD KS VS US OS OPS DP I J) L ∧ I.toNat < C.toNat ∧ J.toNat < C.toNat ∧
    DMI (occM D B M0 US) M0 T KL SD C N KS VS US OS OPS M

/-- The loop state at an occupied cursor `j`. -/
def DLO (D : BitVec 64 → Prop) (B : Bool) (M0 : Mem) (T Kk KL SD C N KS VS US OS OPS DP : BitVec 64)
    (L : GA) (M : Mem) (_ : GA) : Prop :=
  ∃ I J : BitVec 64, LK (dL T Kk C KL SD KS VS US OS OPS DP I J) L ∧ I.toNat < C.toNat ∧ J.toNat < C.toNat ∧
    DMI (occM D B M0 US) M0 T KL SD C N KS VS US OS OPS M ∧ occM D B M0 US J ≠ some 0

theorem dli_update {D : BitVec 64 → Prop} {B : Bool} {M0 : Mem} {T Kk KL SD C N KS VS US OS OPS DP : BitVec 64}
    {x : MlS} (hx : x ∉ dNames) {L : GA} {M : Mem} {G : GA} (v : ValueHOL 64) (G' : GA)
    (h : DLI D B M0 T Kk KL SD C N KS VS US OS OPS DP L M G) :
    DLI D B M0 T Kk KL SD C N KS VS US OS OPS DP (L.update (x,v)) M G' := by
  obtain ⟨I,J,hl,r⟩ := h
  exact ⟨I,J,lk_update hl x v (dL_fresh hx _ _ _ _ _ _ _ _ _ _ _ _ _),r⟩

theorem dli_res {D : BitVec 64 → Prop} {B : Bool} {M0 : Mem} {T Kk KL SD C N KS VS US OS OPS DP : BitVec 64}
    {x : MlS} (hx : x ∉ dNames) {L : GA} {M : Mem} {G : GA} (o : Option (ValueHOL 64)) (G' : GA)
    (h : DLI D B M0 T Kk KL SD C N KS VS US OS OPS DP L M G) :
    DLI D B M0 T Kk KL SD C N KS VS US OS OPS DP (L.resVarEq (x,o)) M G' := by
  obtain ⟨I,J,hl,r⟩ := h
  exact ⟨I,J,lk_res hl x o (dL_fresh hx _ _ _ _ _ _ _ _ _ _ _ _ _),r⟩

theorem dlo_update {D : BitVec 64 → Prop} {B : Bool} {M0 : Mem} {T Kk KL SD C N KS VS US OS OPS DP : BitVec 64}
    {x : MlS} (hx : x ∉ dNames) {L : GA} {M : Mem} {G : GA} (v : ValueHOL 64) (G' : GA)
    (h : DLO D B M0 T Kk KL SD C N KS VS US OS OPS DP L M G) :
    DLO D B M0 T Kk KL SD C N KS VS US OS OPS DP (L.update (x,v)) M G' := by
  obtain ⟨I,J,hl,r⟩ := h
  exact ⟨I,J,lk_update hl x v (dL_fresh hx _ _ _ _ _ _ _ _ _ _ _ _ _),r⟩

/-- Programs made of `skip`, conditionals and assignments to the one local `x`. -/
def locOnly (x : MlS) : ProgHOL 64 → Bool
  | .skip => true
  | .assign .local y _ => decide (y = x)
  | .ite _ a b => locOnly x a && locOnly x b
  | _ => false

theorem aqgd_locOnly {Pr : GA → Mem → GA → Prop} (x : MlS) (hpr : ∀ L M G v, Pr L M G → Pr (L.update (x,v)) M G) :
    ∀ p : ProgHOL 64, locOnly x p = true → AQGD D B A w Vn Pr Pr RR p
  | .skip, _ => aqgd_skip
  | .assign .local y e, h => by
    simp only [locOnly,decide_eq_true_eq] at h
    subst h
    exact aqgd_assignLocal _ _ (fun s v _ _ pre _ _ => hpr _ _ _ _ pre)
  | .assign .global _ _, h => by simp [locOnly] at h
  | .ite c a b, h => by
    simp only [locOnly,Bool.and_eq_true] at h
    exact aqgd_iteD (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) c
      (fun _ _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩)
      (aqgd_conseq (aqgd_locOnly x hpr a h.1) (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
      (aqgd_conseq (aqgd_locOnly x hpr b h.2) (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
  | .dec .., h | .primitive .., h | .store .., h | .store32 .., h | .storeByte .., h | .seq .., h | .while .., h
  | .break, h | .continue, h | .call .., h | .decCall .., h | .extCall .., h | .raise .., h | .return .., h
  | .shMemLoad .., h | .shMemStore .., h | .tick, h | .annot .., h => by simp [locOnly] at h

#print axioms aqgd_locOnly

theorem locOnly_movable : locOnly (ofString "movable") htabDelMovable = true := by decide

theorem ev_var {F : Type} (s : PanSemStateFiniteExact 64 F) (x : MlS) (y : BitVec 64)
    (hx : s.locals.lookup x = some (.val (.word y))) (v : ValueHOL 64) (ev : EV s (.var .local x) = some v) :
    v = .val (.word y) := by
  simp [EV,evalHOLExact,hx] at ev; exact ev.symm

/-- The key slot window of slot `I` lies inside the keys array. -/
theorem kwin {T KL SD C KS VS US OS OPS : BitVec 64} {b : Nat} (rg : DReg T KL SD C KS VS US OS OPS b)
    (I : BitVec 64) (hI : I.toNat < C.toNat) (x : BitVec 64) (hx : MWin (KS + I * SD) KL.toNat x) :
    KS.toNat ≤ x.toNat ∧ x.toNat < KS.toNat + C.toNat * SD.toNat := by
  have kb := rg.kb; have ub := rg.ub; have ob := rg.ob; have eb := rg.eb; have fits := rg.fits
  have mono : I.toNat * SD.toNat + SD.toNat ≤ C.toNat * SD.toNat := by
    have := Nat.mul_le_mul_right SD.toNat (Nat.succ_le_of_lt hI); rw [Nat.succ_mul] at this; exact this
  have eD : (KS + I * SD).toNat = KS.toNat + I.toNat * SD.toNat := toNat_add_mul KS I SD (by omega)
  have al : (KS + I * SD).toNat % 8 = 0 := by
    rw [eD]; have := rg.ka; have := rg.sa
    rw [Nat.add_mod,Nat.mul_mod]; simp [*]
  have := mwin_ge hx al (by omega)
  omega

theorem kl_small {T KL SD C KS VS US OS OPS : BitVec 64} {b : Nat} (rg : DReg T KL SD C KS VS US OS OPS b) :
    KL.toNat + 32 < 2 ^ 64 := by
  have kb := rg.kb; have ub := rg.ub; have ob := rg.ob; have eb := rg.eb; have fits := rg.fits
  have c1 : 1 ≤ C.toNat := by rw [rg.pow]; exact Nat.one_le_two_pow
  have : SD.toNat ≤ C.toNat * SD.toNat := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- The move step's state with the loaded order position `moved_pos`. -/
def DLX (D : BitVec 64 → Prop) (B : Bool) (M0 : Mem) (T Kk KL SD C N KS VS US OS OPS DP : BitVec 64)
    (L : GA) (M : Mem) (_ : GA) : Prop :=
  ∃ I J X : BitVec 64,
      LK ((ofString "moved_pos",X) :: dL T Kk C KL SD KS VS US OS OPS DP I J) L ∧ I.toNat < C.toNat ∧
      J.toNat < C.toNat ∧ X.toNat < C.toNat ∧ DMI (occM D B M0 US) M0 T KL SD C N KS VS US OS OPS M

section move
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {M0 : Mem} {T Kk KL SD C N KS VS US OS OPS DP : BitVec 64} {b : Nat}

/-- The original backward-shift move step: memcpy of the key, value copy, order relink, `i := j`. -/
theorem del_move (rg : DReg T KL SD C KS VS US OS OPS b) (nC : N.toNat ≤ C.toNat)
    (hw : ¬ InTabF T KS SD C US VS OS OPS w) :
    AQGD D B A w (fun _ => True) (fun L M G => DLO D B M0 T Kk KL SD C N KS VS US OS OPS DP L M G ∧ True)
      (DLI D B M0 T Kk KL SD C N KS VS US OS OPS DP) RR htabDelMove := by
  have hk := rg.hk; have hv := rg.hv; have kb := rg.kb; have vb := rg.vb; have ub := rg.ub; have ob := rg.ob
  have eb := rg.eb
  rw [htabDelMove_shape]
  refine aqgd_seq (Q := DLO D B M0 T Kk KL SD C N KS VS US OS OPS DP) (aqgd_callSpec (Vn' := fun _ => False)
    (Pe := fun L0 M0' H0 L M H => ∃ I S : BitVec 64, L0.lookup (ofString "i") = some (.val (.word I)) ∧
      L.lookup (ofString "dst") = some (.val (.word (KS + I * SD))) ∧ L.lookup (ofString "src") = some (.val (.word S)) ∧
      L.lookup (ofString "n") = some (.val (.word KL)) ∧ M = M0' ∧ H = H0)
    (RRe := fun L0 M0' _ _ M' _ => ∀ I : BitVec 64, L0.lookup (ofString "i") = some (.val (.word I)) →
      ∀ x, ¬ MWin (KS + I * SD) KL.toNat x → M' x = M0' x)
    _ _ _ _ _ originalRuntimeCode_memcpy_lookup (by simp) ?_ ?_ ?_) ?_
  · intro L0 M0' H0 ⟨⟨I,J,hl,hI,_,_,_⟩,_⟩
    have hi := lk_get hl (ofString "i") I (by simp [dL])
    refine aqgd_conseq (aqgd_of_window (Pe := fun L _ => ∃ S : BitVec 64,
        L.lookup (ofString "dst") = some (.val (.word (KS + I * SD))) ∧ L.lookup (ofString "src") = some (.val (.word S)) ∧
        L.lookup (ofString "n") = some (.val (.word KL)))
      memcpy_body_globals_frame (by body_check Guest.guestFn_memcpy) (by body_check Guest.guestFn_memcpy)
      (MWin (KS + I * SD) KL.toNat)
      (fun s _ ⟨S,hd,hs,hn⟩ x hx => memcpy_body_window s _ S KL x hd hs hn (kl_small rg) hx)
      (fun h' => hw (Or.inr (Or.inl (kwin rg I hI w h')))) M0' H0) ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M H ⟨I',S,hI',hd,hs,hn,hm,hh⟩
      rw [hi] at hI'; cases hI'
      exact ⟨⟨S,hd,hs,hn⟩,hm,hh⟩
    · intro v M' H' ⟨_,h⟩ I' hI' x hx
      rw [hi] at hI'; cases hI'
      exact h x hx
  · intro F s values callee rs _ H _ ⟨⟨I,J,hl,hI,hJ,hm,ho⟩,_⟩ _ args lookup
    have hks := lk_get hl (ofString "keys") KS (by simp [dL,dB])
    have hi := lk_get hl (ofString "i") I (by simp [dL])
    have hj := lk_get hl (ofString "j") J (by simp [dL])
    have hsd := lk_get hl (ofString "stride") SD (by simp [dL,dB])
    have hkl := lk_get hl (ofString "klen") KL (by simp [dL,dB])
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hks,hi,hj,hsd,hkl,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord] at args
    subst args
    rw [pan_three_word_lookup _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
      originalRuntimeCode_memcpy_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨I,KS + J * SD,hi,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
      by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
      by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl,rfl⟩
  · intro L M H v M' H' ⟨⟨I,J,hl,hI,hJ,hm,ho⟩,_⟩ h
    have hi := lk_get hl (ofString "i") I (by simp [dL])
    exact ⟨I,J,hl,hI,hJ,dmi_low rg nC hm M' (fun x hx => h I hi x (fun h' => by
      have := kwin rg I hI x h'; omega)),ho⟩
  refine aqgd_seq (Q := DLO D B M0 T Kk KL SD C N KS VS US OS OPS DP) (aqgd_storeD _ _ ?_ ?_) ?_
  · intro F s H _ _ _ ⟨I,J,hl,hI,hJ,hm,ho⟩ _
    have hvs := lk_get hl (ofString "vals") VS (by simp [dL,dB])
    have hi := lk_get hl (ofString "i") I (by simp [dL])
    have ea := add_mul8_toNat VS I C hI (by omega)
    refine ⟨VS + I * 8,eval_delScaled8 s _ _ VS I hvs hi,fun e => hw (Or.inr (Or.inr (Or.inl ⟨by rw [e,ea]; omega,
      by rw [e,ea]; omega⟩))),fun y _ => ⟨I,J,hl,hI,hJ,dmi_write rg nC hm _ (by rw [ea]; omega) (by rw [ea]; omega) _
        (fun x hx => word_update_keep x hx),ho⟩⟩
  · intro F s x H _ _ _ _ _ ev
    exact ev_load_one_word s _ x ev
  refine aqgd_decD (Pb := DLX D B M0 T Kk KL SD C N KS VS US OS OPS DP)
    (Qb := DLI D B M0 T Kk KL SD C N KS VS US OS OPS DP) _ _ _ (fun _ => rfl) ?_ ?_
    (fun L M H L' M' H' _ q => dli_res (by decide) _ _ q)
  · intro F s v H _ _ _ ⟨I,J,hl,hI,hJ,hm,ho⟩ _ ev _
    have hops := lk_get hl (ofString "order_pos") OPS (by simp [dL,dB])
    have hj := lk_get hl (ofString "j") J (by simp [dL])
    have e := ev_load_at s _ _ (eval_delScaled8 s _ _ OPS J hops hj) v ev
    obtain ⟨X,hX,xl⟩ := hm.2.1 J hJ ho
    rw [hX] at e; subst e
    exact ⟨I,J,X,lk_cons hl _ _ (dL_fresh (by decide) _ _ _ _ _ _ _ _ _ _ _ _ _),hI,hJ,xl,hm⟩
  refine aqgd_seq (Q := DLX D B M0 T Kk KL SD C N KS VS US OS OPS DP) (aqgd_storeD _ _ ?_ ?_)
    (aqgd_seq (Q := DLX D B M0 T Kk KL SD C N KS VS US OS OPS DP) (aqgd_storeD _ _ ?_ ?_) (aqgd_assignLocal _ _ ?_))
  · intro F s H _ _ _ ⟨I,J,X,hl,hI,hJ,xl,hm⟩ _
    have hos := lk_get hl (ofString "order") OS (by simp [dL,dB])
    have hx := lk_get hl (ofString "moved_pos") X (by simp)
    have hi := lk_get hl (ofString "i") I (by simp [dL])
    have ea := add_mul8_toNat OS X C xl (by omega)
    refine ⟨OS + X * 8,eval_delScaled8 s _ _ OS X hos hx,fun e => hw (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨by rw [e,ea]; omega,by rw [e,ea]; omega⟩))))),fun y hy => ?_⟩
    have := ev_var s _ _ hi _ hy; cases this
    exact ⟨I,J,X,hl,hI,hJ,xl,dmi_write_order rg nC hm X I xl hI⟩
  · intro F s x H _ _ _ ⟨I,J,X,hl,_⟩ _ ev
    exact ⟨I,ev_var s _ _ (lk_get hl (ofString "i") I (by simp [dL])) _ ev⟩
  · intro F s H _ _ _ ⟨I,J,X,hl,hI,hJ,xl,hm⟩ _
    have hops := lk_get hl (ofString "order_pos") OPS (by simp [dL,dB])
    have hx := lk_get hl (ofString "moved_pos") X (by simp)
    have hi := lk_get hl (ofString "i") I (by simp [dL])
    have ea := add_mul8_toNat OPS I C hI (by omega)
    refine ⟨OPS + I * 8,eval_delScaled8 s _ _ OPS I hops hi,fun e => hw (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨by rw [e,ea]; omega,by rw [e,ea]; omega⟩))))),fun y hy => ?_⟩
    have := ev_var s _ _ hx _ hy; cases this
    exact ⟨I,J,X,hl,hI,hJ,xl,dmi_write_opos rg nC hm I X hI xl⟩
  · intro F s x H _ _ _ ⟨I,J,X,hl,_⟩ _ ev
    exact ⟨X,ev_var s _ _ (lk_get hl (ofString "moved_pos") X (by simp)) _ ev⟩
  · intro F s v _ _ ⟨I,J,X,hl,hI,hJ,xl,hm⟩ _ ev
    have := ev_var s _ _ (lk_get hl (ofString "j") J (by simp [dL])) _ ev; subst this
    exact ⟨J,J,lk_set_i (lk_tail hl) J,hJ,hJ,hm⟩

#print axioms del_move
end move

theorem occM_congr {D : BitVec 64 → Prop} {B : Bool} {M M' : Mem} {US q : BitVec 64}
    (h : M (panByteAlignHOL (US + q)) = M' (panByteAlignHOL (US + q))) : occM D B M US q = occM D B M' US q := by
  unfold occM panMemLoadByteHOL; simp only []; rw [h]

theorem htabHash_mf : MemoryFrame (sourceFunctionBody Guest.guestFn_htab_hash) := memoryFrame_leaf _ htabHash_readOnly

theorem dlo_dli {D : BitVec 64 → Prop} {B : Bool} {M0 : Mem} {T Kk KL SD C N KS VS US OS OPS DP : BitVec 64}
    {L : GA} {M : Mem} {G : GA} (h : DLO D B M0 T Kk KL SD C N KS VS US OS OPS DP L M G) :
    DLI D B M0 T Kk KL SD C N KS VS US OS OPS DP L M G := by
  obtain ⟨I,J,hl,hI,hJ,hm,_⟩ := h; exact ⟨I,J,hl,hI,hJ,hm⟩

section body
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {M0 : Mem} {T Kk KL SD C N KS VS US OS OPS DP : BitVec 64} {b : Nat}

/-- One original backward-shift iteration: probe step, empty-slot break, home hash, movability test and move. -/
theorem del_body (rg : DReg T KL SD C KS VS US OS OPS b) (nC : N.toNat ≤ C.toNat)
    (hw : ¬ InTabF T KS SD C US VS OS OPS w) :
    AQGB D B A w (fun _ => True) (fun L M G => DLI D B M0 T Kk KL SD C N KS VS US OS OPS DP L M G ∧ True)
      (DLI D B M0 T Kk KL SD C N KS VS US OS OPS DP) (DLI D B M0 T Kk KL SD C N KS VS US OS OPS DP) RR htabDelBody := by
  have ub := rg.ub; have ob := rg.ob; have eb := rg.eb
  rw [htabDelBody_shape]
  refine aqgb_seq (Q := DLI D B M0 T Kk KL SD C N KS VS US OS OPS DP) (aqgb_of_aqgd ?_)
    (aqgb_seq (Q := DLO D B M0 T Kk KL SD C N KS VS US OS OPS DP) ?_ (aqgb_of_aqgd ?_))
  · unfold hashProbeStep
    refine aqgd_assignLocal _ _ ?_
    intro F s v _ _ ⟨⟨I,J,hl,hI,hJ,hm⟩,_⟩ _ ev
    have hj := lk_get hl (ofString "j") J (by simp [dL])
    have hc := lk_get hl (ofString "cap") C (by simp [dL,dB])
    simp [EV,evalHOLExact,evalListHOLExact,hj,hc,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
    subst ev
    refine ⟨I,_,lk_cons (lk_tail hl) _ _ ?_,hI,mask_lt' _ C b rg.pow (by omega),hm⟩
    intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · show ofString "i" ≠ ofString "j"; decide
    · exact dB_ne_j _ _ _ _ _ _ _ _ _ _ _ p hp
  · refine aqgb_ite (CT := fun _ _ _ => True)
      (CF := fun L M _ => ∀ J : BitVec 64, L.lookup (ofString "j") = some (.val (.word J)) → occM D B M US J ≠ some 0)
      _ ?_ (aqgb_break (fun _ _ _ h => h.1)) (aqgb_of_aqgd (aqgd_conseq aqgd_skip (fun _ _ _ h => h) ?_ (fun _ _ _ h => h)))
    · intro F s x _ dom ⟨I,J,hl,hI,hJ,hm⟩ _ ev
      refine ⟨fun _ => trivial,fun hx0 J' hJ' => ?_⟩
      have hj := lk_get hl (ofString "j") J (by simp [dL])
      have hu := lk_get hl (ofString "used") US (by simp [dL,dB])
      rw [hj] at hJ'; cases hJ'
      rw [← dom.2.1,← dom.2.2,← occM_eq]
      cases hr : hashOccupancyRead s US J with
      | none => simp
      | some byte =>
        have := eval_delBreakCheck s US J byte hu hj hr
        simp only [EV] at ev
        rw [this] at ev
        simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at ev
        intro h
        simp only [Option.some.injEq] at h
        subst h hx0
        simp at ev
    · intro L M H ⟨⟨I,J,hl,hI,hJ,hm⟩,hcf⟩
      have hj := lk_get hl (ofString "j") J (by simp [dL])
      refine ⟨I,J,hl,hI,hJ,hm,?_⟩
      rw [occM_congr (hm.1 J hJ).symm]
      exact hcf J hj
  · refine aqgd_decCallSpec (Pe := fun _ M0' H0 _ M H => M = M0' ∧ H = H0) (RRe := fun _ M0' H0 _ M H => M = M0' ∧ H = H0)
      (Pc := DLO D B M0 T Kk KL SD C N KS VS US OS OPS DP) (Qc := DLI D B M0 T Kk KL SD C N KS VS US OS OPS DP)
      (Vn' := fun _ => False) _ _ _ _ _ _ _ originalRuntimeCode_hash_lookup (by simp) ?_ ?_ (fun _ => rfl) ?_ ?_
      (fun _ _ _ _ _ _ _ q => dli_res (by decide) _ _ q)
    · intro L0 M0' H0 _
      exact aqgd_conseq (aqgd_of_mf htabHash_mf (by body_check Guest.guestFn_htab_hash)
        (by body_check Guest.guestFn_htab_hash) M0' H0) (fun _ _ _ h => h) (fun _ _ _ _ => trivial) (fun _ _ _ h => h)
    · intro F s values callee rs _ H _ _ _ _ _
      exact ⟨rfl,rfl⟩
    · intro L M H v M' H' pre ⟨hm,_⟩ _
      subst hm
      exact dlo_update (by decide) v H' pre
    refine aqgd_decD (Pb := DLO D B M0 T Kk KL SD C N KS VS US OS OPS DP)
      (Qb := DLI D B M0 T Kk KL SD C N KS VS US OS OPS DP) _ _ _ (fun _ => rfl)
      (fun s v H _ _ _ pre _ _ _ => dlo_update (by decide) v H pre) ?_ (fun _ _ _ _ _ _ _ q => dli_res (by decide) _ _ q)
    refine aqgd_decD (Pb := DLO D B M0 T Kk KL SD C N KS VS US OS OPS DP)
      (Qb := DLI D B M0 T Kk KL SD C N KS VS US OS OPS DP) _ _ _ (fun _ => rfl)
      (fun s v H _ _ _ pre _ _ _ => dlo_update (by decide) v H pre) ?_ (fun _ _ _ _ _ _ _ q => dli_res (by decide) _ _ q)
    refine aqgd_seq (Q := DLO D B M0 T Kk KL SD C N KS VS US OS OPS DP)
      (aqgd_locOnly _ (fun L M G v h => dlo_update (by decide) v G h) _ locOnly_movable) ?_
    exact aqgd_iteD (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
      (fun _ _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (del_move rg nC hw)
      (aqgd_conseq aqgd_skip (fun _ _ _ h => h) (fun _ _ _ h => dlo_dli h.1) (fun _ _ _ h => h))

#print axioms del_body
end body

theorem aqgd_ex {α : Sort _} {P : α → GA → Mem → GA → Prop} {Q : GA → Mem → GA → Prop} {p : ProgHOL 64}
    (h : ∀ a, AQGD D B A w Vn (P a) Q RR p) : AQGD D B A w Vn (fun L M G => ∃ a, P a L M G) Q RR p :=
  fun F s code dom aw sl G hG ⟨a,pre⟩ => h a F s code dom aw sl G hG pre

/-- Tail state: extra locals `ex` above the loop locals, the order-list facts and header. -/
def DT (T Kk KL SD C N KS VS US OS OPS DP : BitVec 64) (ex : List (MlS × BitVec 64)) (L : GA) (M : Mem) (_ : GA) :
    Prop :=
  ∃ I J : BitVec 64, ∃ M1 : Mem, LK (ex ++ dL T Kk C KL SD KS VS US OS OPS DP I J) L ∧ I.toNat < C.toNat ∧
    DMI (fun _ => some 0) M1 T KL SD C N KS VS US OS OPS M

section tail
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {M0 : Mem} {T Kk KL SD C N KS VS US OS OPS DP : BitVec 64} {b : Nat}

/-- The original post-loop tail: clear the hole's occupancy byte, move the last order entry into the deleted
position, store the decremented count and return. -/
theorem del_tail (rg : DReg T KL SD C KS VS US OS OPS b) (nC : N.toNat ≤ C.toNat) (hn1 : 1 ≤ N.toNat)
    (hdp : DP.toNat < C.toNat) (hw : ¬ InTabF T KS SD C US VS OS OPS w) :
    AQGD D B A w (fun _ => True)
      (fun L M G => DLI D B M0 T Kk KL SD C N KS VS US OS OPS DP L M G ∨ DLI D B M0 T Kk KL SD C N KS VS US OS OPS DP L M G)
      (fun _ _ _ => True) (fun _ _ _ => True) htabDelTail := by
  have hk := rg.hk; have kb := rg.kb; have ub := rg.ub; have ob := rg.ob; have eb := rg.eb
  have fitT : T.toNat + 72 < 2 ^ 64 := by omega
  rw [htabDelTail_shape]
  refine aqgd_seq (Q := DT T Kk KL SD C N KS VS US OS OPS DP []) (aqgd_storeByte _ _ ?_) ?_
  · intro F s _ _ pre _
    obtain ⟨I,J,hl,hI,hJ,hm⟩ := pre.elim id id
    have hu := lk_get hl (ofString "used") US (by simp [dL,dB])
    have hi := lk_get hl (ofString "i") I (by simp [dL])
    have bl := byteAlign_lt (C := C) rg.ua (by omega) hI
    refine ⟨US + I,by simp [EV,evalHOLExact,evalListHOLExact,hu,hi,wordOpHOL,wordOp,valueIsWord,valueWord],
      fun e => hw (Or.inr (Or.inr (Or.inr (Or.inl ⟨by rw [e]; exact bl.1,by rw [e]; exact bl.2⟩)))),
      fun M' hM' => ⟨I,J,M',hl,hI,dmi_reset rg nC hm _ bl.1 bl.2 M' hM'⟩⟩
  refine aqgd_decD (Pb := DT T Kk KL SD C N KS VS US OS OPS DP [(ofString "n",N)]) (Qb := fun _ _ _ => True)
    _ _ _ (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ _ _ => trivial)
  · intro F s v H _ _ _ ⟨I,J,M1,hl,hI,hm⟩ _ ev _
    have ht := lk_get hl (ofString "t") T (by simp [dL,dB])
    obtain ⟨_,_,_,h24,_⟩ := hm.2.2.2
    have h24' : s.memory (T + 24) = .word N := h24
    rw [ev_load_off s _ T 24 v ht ev,h24']
    exact ⟨I,J,M1,lk_cons hl _ _ (by simp only [dL,dB,List.nil_append]; lkne),hI,hm⟩
  refine aqgd_decD (Pb := DT T Kk KL SD C N KS VS US OS OPS DP [(ofString "last_pos",N - 1),(ofString "n",N)])
    (Qb := fun _ _ _ => True) _ _ _ (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ _ _ => trivial)
  · intro F s v H _ _ _ ⟨I,J,M1,hl,hI,hm⟩ _ ev _
    have hn := lk_get hl (ofString "n") N (by simp)
    simp [EV,evalHOLExact,evalListHOLExact,hn,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
    subst ev
    exact ⟨I,J,M1,lk_cons hl _ _ (by simp only [dL,dB,List.cons_append,List.nil_append]; lkne),hI,hm⟩
  refine aqgd_seq (Q := DT T Kk KL SD C N KS VS US OS OPS DP [(ofString "last_pos",N - 1),(ofString "n",N)])
    (aqgd_iteD (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
      (fun _ _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) ?_ (aqgd_conseq aqgd_skip (fun _ _ _ h => h.1)
        (fun _ _ _ h => h) (fun _ _ _ h => h))) ?_
  · have pN : (N - 1).toNat < N.toNat := by
      rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)]; simp; omega
    refine aqgd_decD (Pb := fun L M G => ∃ X : BitVec 64, X.toNat < C.toNat ∧
        DT T Kk KL SD C N KS VS US OS OPS DP [(ofString "last_slot",X),(ofString "last_pos",N - 1),(ofString "n",N)] L M G)
      (Qb := fun L M G => ∃ X : BitVec 64,
        DT T Kk KL SD C N KS VS US OS OPS DP [(ofString "last_slot",X),(ofString "last_pos",N - 1),(ofString "n",N)] L M G)
      _ _ _ (fun _ => rfl) ?_ ?_ ?_
    · intro F s v H _ _ _ ⟨⟨I,J,M1,hl,hI,hm⟩,_⟩ _ ev _
      have hos := lk_get hl (ofString "order") OS (by simp [dL,dB])
      have hlp := lk_get hl (ofString "last_pos") (N - 1) (by simp)
      have e := ev_load_at s _ _ (eval_delScaled8 s _ _ OS (N - 1) hos hlp) v ev
      obtain ⟨X,hX,xl⟩ := hm.2.2.1 (N - 1) pN
      rw [hX] at e; subst e
      exact ⟨X,xl,I,J,M1,lk_cons hl _ _ (by simp only [dL,dB,List.cons_append,List.nil_append]; lkne),hI,hm⟩
    · refine aqgd_ex (fun X => ?_)
      refine aqgd_seq (Q := fun L M G => X.toNat < C.toNat ∧
          DT T Kk KL SD C N KS VS US OS OPS DP [(ofString "last_slot",X),(ofString "last_pos",N - 1),(ofString "n",N)] L M G)
        (aqgd_storeD _ _ ?_ ?_) (aqgd_storeD _ _ ?_ ?_)
      · intro F s H _ _ _ ⟨xl,I,J,M1,hl,hI,hm⟩ _
        have hos := lk_get hl (ofString "order") OS (by simp [dL,dB])
        have hd := lk_get hl (ofString "deleted_pos") DP (by simp [dL,dB])
        have hx := lk_get hl (ofString "last_slot") X (by simp)
        have ea := add_mul8_toNat OS DP C hdp (by omega)
        refine ⟨OS + DP * 8,eval_delScaled8 s _ _ OS DP hos hd,fun e => hw (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨by rw [e,ea]; omega,by rw [e,ea]; omega⟩))))),fun y hy => ?_⟩
        have := ev_var s _ _ hx _ hy; cases this
        exact ⟨xl,I,J,M1,hl,hI,dmi_write_order rg nC hm DP X hdp xl⟩
      · intro F s x H _ _ _ ⟨xl,I,J,M1,hl,_⟩ _ ev
        exact ⟨X,ev_var s _ _ (lk_get hl (ofString "last_slot") X (by simp)) _ ev⟩
      · intro F s H _ _ _ ⟨xl,I,J,M1,hl,hI,hm⟩ _
        have hops := lk_get hl (ofString "order_pos") OPS (by simp [dL,dB])
        have hd := lk_get hl (ofString "deleted_pos") DP (by simp [dL,dB])
        have hx := lk_get hl (ofString "last_slot") X (by simp)
        have ea := add_mul8_toNat OPS X C xl (by omega)
        refine ⟨OPS + X * 8,eval_delScaled8 s _ _ OPS X hops hx,fun e => hw (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨by rw [e,ea]; omega,by rw [e,ea]; omega⟩))))),fun y hy => ?_⟩
        have := ev_var s _ _ hd _ hy; cases this
        exact ⟨X,I,J,M1,hl,hI,dmi_write_opos rg nC hm X DP xl hdp⟩
      · intro F s x H _ _ _ ⟨xl,I,J,M1,hl,_⟩ _ ev
        exact ⟨DP,ev_var s _ _ (lk_get hl (ofString "deleted_pos") DP (by simp [dL,dB])) _ ev⟩
    · intro L M H L' M' H' _ ⟨X,I,J,M1,hl,hI,hm⟩
      exact ⟨I,J,M1,lk_res (lk_tail hl) _ _ (by simp only [dL,dB,List.cons_append,List.nil_append]; lkne),hI,hm⟩
  refine aqgd_seq (Q := fun _ _ _ => True) (aqgd_storeD _ _ ?_ ?_) (aqgd_returnD _ (fun _ _ _ _ _ _ _ _ _ => trivial))
  · intro F s H _ _ _ ⟨I,J,M1,hl,hI,hm⟩ _
    have ht := lk_get hl (ofString "t") T (by simp [dL,dB])
    have e24 : (T + (24 : BitVec 64)).toNat = T.toNat + 24 := by rw [BitVec.toNat_add_of_lt] <;> simp <;> omega
    refine ⟨T + 24,by simp [EV,hashLocalAddress,evalHOLExact,evalListHOLExact,ht,wordOpHOL,wordOp,valueIsWord,valueWord],
      fun e => hw (Or.inl ⟨by rw [e,e24]; omega,by rw [e,e24]; omega⟩),fun _ _ => trivial⟩
  · intro F s x H _ _ _ ⟨I,J,M1,hl,_⟩ _ ev
    exact ⟨N - 1,ev_var s _ _ (lk_get hl (ofString "last_pos") (N - 1) (by simp)) _ ev⟩

end tail

theorem aqgd_purePre {φ : Prop} {P Q : GA → Mem → GA → Prop} {p : ProgHOL 64} (h : φ → AQGD D B A w Vn P Q RR p) :
    AQGD D B A w Vn (fun L M G => P L M G ∧ φ) Q RR p :=
  fun F s code dom aw sl G hG ⟨pre,f⟩ => h f F s code dom aw sl G hG pre

theorem lk_sub {l l' : List (MlS × BitVec 64)} {L : GA} (h : LK l L) (sub : ∀ p ∈ l', p ∈ l) : LK l' L :=
  fun p hp => h p (sub p hp)

section main
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64}

set_option maxHeartbeats 4000000 in
/-- All-outcome watched-word frame of the original `htab_del` body on an aligned table with `OrderInv` and
`count < capacity`, in the fixed-domain triple: the memory word `w` outside the table's header and five arrays is
unchanged in every outcome (normal, returned, error, timeout). The table is described by a witness state `s0`
whose memory is the entry memory and whose domain/endianness are `D`/`B`. -/
theorem del_aqgd {F0 : Type} (s0 : PanSemStateFiniteExact 64 F0) {KL T KS SD C US VS OS OPS N : BitVec 64} {b : Nat}
    (Kk : BitVec 64) (inv : HtabAligned KL T KS SD C US VS OS OPS N b s0) (oi : OrderInv s0 C N US OS OPS)
    (hD : s0.memaddrs = D) (hB : s0.be = B) (room : N.toNat < C.toNat)
    (hw : ¬ InTabF T KS SD C US VS OS OPS w) :
    AQGD D B A w (fun _ => True) (fun L M _ => LK [(ofString "key",Kk),(ofString "t",T)] L ∧ M = s0.memory)
      (fun _ _ _ => True) (fun _ _ _ => True) (sourceFunctionBody Guest.guestFn_htab_del) := by
  have rg := dreg_of_aligned inv
  have hk := rg.hk; have kb := rg.kb; have ub := rg.ub; have ob := rg.ob; have eb := rg.eb
  have occE : ∀ q, occM D B s0.memory US q = hashOccupancyRead s0 US q := fun q => by rw [occM_eq,hD,hB]
  have hdr : Hdr s0.memory T KL SD C N KS VS US OS OPS :=
    ⟨inv.cell0,inv.cell8,inv.cell16,inv.cell24,inv.cell32,inv.cell40,inv.cell48,inv.cell56,inv.cell64⟩
  have ta := inv.tableAligned
  have dom16 : D (T + 16) := by
    rw [← hD]
    have e : (T + (16 : BitVec 64)).toNat = T.toNat + 16 := by rw [BitVec.toNat_add_of_lt] <;> simp <;> omega
    exact inv.domain _ (by rw [e]; omega) (by rw [e]; omega) (by rw [e]; omega)
  have dom48 : D (T + 48) := by
    rw [← hD]
    have e : (T + (48 : BitVec 64)).toNat = T.toNat + 48 := by rw [BitVec.toNat_add_of_lt] <;> simp <;> omega
    exact inv.domain _ (by rw [e]; omega) (by rw [e]; omega) (by rw [e]; omega)
  rw [source_htabDel_body]
  refine aqgd_decCallSpec (Vn' := fun _ => False)
    (Pe := fun _ M0' H0 L M H => M = M0' ∧ H = H0 ∧ L.lookup (ofString "t") = some (.val (.word T)) ∧ M0' = s0.memory)
    (RRe := fun _ M0' H0 v M H => M = M0' ∧ H = H0 ∧ ∃ i : BitVec 64, v = .val (.word i) ∧
      (i = C ∨ (i.toNat < C.toNat ∧ occM D B s0.memory US i ≠ some 0)))
    (Pc := fun L M _ => ∃ I : BitVec 64, LK [(ofString "i",I),(ofString "key",Kk),(ofString "t",T)] L ∧
      (M = s0.memory ∧ (I = C ∨ (I.toNat < C.toNat ∧ occM D B s0.memory US I ≠ some 0))))
    (Qc := fun _ _ _ => True) _ _ _ _ _ _ _ originalRuntimeCode_hashFind_lookup (by simp) ?_ ?_ (fun _ => rfl) ?_ ?_
    (fun _ _ _ _ _ _ _ _ => trivial)
  · intro L0 M0' H0 _
    have base := aqgd_conseq (D := D) (B := B) (A := A) (w := w)
      (P' := fun L M H => M = M0' ∧ H = H0 ∧ L.lookup (ofString "t") = some (.val (.word T)) ∧ M0' = s0.memory)
      (aqgd_of_mf htabFindSlot_memoryFrame (by body_check Guest.guestFn_htab_find_slot)
        (by body_check Guest.guestFn_htab_find_slot) M0' H0) (fun _ _ _ h => ⟨h.1,h.2.1⟩) (fun _ _ _ _ => trivial)
      (fun _ _ _ h => h)
    have aug := aqgd_augment base (X := fun v _ _ => ∃ i : BitVec 64, v = .val (.word i) ∧
      (i = C ∨ (i.toNat < C.toNat ∧ occM D B s0.memory US i ≠ some 0))) (by
      intro F s code dom ⟨hm,_,ht,he⟩ v post run
      have hmem : s.memory = s0.memory := hm.trans he
      obtain ⟨i,hv,hi⟩ := htabFindSlot_returned_occupied s post T C US b inv.power code ht
        (by rw [dom.2.1]; exact dom16) (by rw [hmem]; exact inv.cell16) (by rw [dom.2.1]; exact dom48)
        (by rw [hmem]; exact inv.cell48) v run
      refine ⟨i,hv,hi.imp id (fun h => ⟨h.1,?_⟩)⟩
      rw [occM_eq,dom.2.1,dom.2.2,hmem] at h
      exact h.2)
    exact aqgd_conseq aug (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ ⟨⟨h1,h2⟩,h3⟩ => ⟨h1,h2,h3⟩)
  · intro F s values callee rs _ H hH ⟨hl,hm⟩ _ args lookup
    have ht := lk_get hl (ofString "t") T (by simp)
    have hkk := lk_get hl (ofString "key") Kk (by simp)
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,ht,hkk] at args
    subst args
    rw [pan_two_word_lookup _ _ _ _ _ _ _ (by decide) originalRuntimeCode_hashFind_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨rfl,rfl,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],hm⟩
  · intro L M H v M' H' ⟨hl,hm⟩ ⟨hM',_,i,hv,hi⟩ _
    subst hv
    exact ⟨i,lk_cons hl _ _ (by lkne),hM'.trans hm,hi⟩
  refine aqgd_ex (fun I0 => ?_)
  refine aqgd_hdrDec (T := T) (Rm := fun M => M = s0.memory ∧ (I0 = C ∨ (I0.toNat < C.toNat ∧ occM D B s0.memory US I0 ≠ some 0)))
    (Qb := fun _ _ _ => True) (ofString "cap") 16 C (by lkne) (by simp) (fun M h => by rw [h.1]; exact hdr.2.2.1) ?_
    (fun _ _ _ _ _ _ _ _ => trivial)
  refine aqgd_seq (Q := fun L M _ => LK [(ofString "cap",C),(ofString "i",I0),(ofString "key",Kk),(ofString "t",T)] L ∧
      (M = s0.memory ∧ I0.toNat < C.toNat ∧ occM D B s0.memory US I0 ≠ some 0)) ?_ ?_
  · unfold htabDelMissing
    refine aqgd_iteD (CT := fun _ _ _ => I0 = C) (CF := fun _ _ _ => I0 ≠ C) _ ?_
      (aqgd_returnD _ (fun _ _ _ _ _ _ _ _ _ => trivial)) (aqgd_conseq aqgd_skip (fun _ _ _ h => h) ?_ (fun _ _ _ h => h))
    · intro F s x H _ _ _ ⟨hl,_⟩ _ ev
      have hi := lk_get hl (ofString "i") I0 (by simp)
      have hc := lk_get hl (ofString "cap") C (by simp)
      simp [EV,evalHOLExact,evalListHOLExact,hi,hc] at ev
      simp only [Compiler.Encoders.Asm.wordCmpHOL] at ev
      by_cases e : I0 = C
      · subst e; simp at ev; subst ev; exact ⟨fun _ => rfl,fun h => absurd h (by decide)⟩
      · simp [e] at ev; subst ev; exact ⟨fun h => absurd rfl h,fun _ => e⟩
    · intro L M H ⟨⟨hl,hm,hi⟩,ne⟩
      exact ⟨hl,hm,hi.resolve_left ne⟩
  refine aqgd_hdrDec (T := T) (Qb := fun _ _ _ => True) (ofString "klen") 0 KL (by lkne) (by simp)
    (fun M h => by rw [h.1]; exact hdr.1) ?_ (fun _ _ _ _ _ _ _ _ => trivial)
  refine aqgd_hdrDec (T := T) (Qb := fun _ _ _ => True) (ofString "stride") 8 SD (by lkne) (by simp)
    (fun M h => by rw [h.1]; exact hdr.2.1) ?_ (fun _ _ _ _ _ _ _ _ => trivial)
  refine aqgd_hdrDec (T := T) (Qb := fun _ _ _ => True) (ofString "keys") 32 KS (by lkne) (by simp)
    (fun M h => by rw [h.1]; exact hdr.2.2.2.2.1) ?_ (fun _ _ _ _ _ _ _ _ => trivial)
  refine aqgd_hdrDec (T := T) (Qb := fun _ _ _ => True) (ofString "vals") 40 VS (by lkne) (by simp)
    (fun M h => by rw [h.1]; exact hdr.2.2.2.2.2.1) ?_ (fun _ _ _ _ _ _ _ _ => trivial)
  refine aqgd_hdrDec (T := T) (Qb := fun _ _ _ => True) (ofString "used") 48 US (by lkne) (by simp)
    (fun M h => by rw [h.1]; exact hdr.2.2.2.2.2.2.1) ?_ (fun _ _ _ _ _ _ _ _ => trivial)
  refine aqgd_hdrDec (T := T) (Qb := fun _ _ _ => True) (ofString "order") 56 OS (by lkne) (by simp)
    (fun M h => by rw [h.1]; exact hdr.2.2.2.2.2.2.2.1) ?_ (fun _ _ _ _ _ _ _ _ => trivial)
  refine aqgd_hdrDec (T := T) (Qb := fun _ _ _ => True) (ofString "order_pos") 64 OPS (by lkne) (by simp)
    (fun M h => by rw [h.1]; exact hdr.2.2.2.2.2.2.2.2) ?_ (fun _ _ _ _ _ _ _ _ => trivial)
  refine aqgd_conseq (aqgd_purePre (P := fun L M _ => LK [(ofString "order_pos",OPS),(ofString "order",OS),
      (ofString "used",US),(ofString "vals",VS),(ofString "keys",KS),(ofString "stride",SD),(ofString "klen",KL),
      (ofString "cap",C),(ofString "i",I0),(ofString "key",Kk),(ofString "t",T)] L ∧ M = s0.memory)
      (φ := I0.toNat < C.toNat ∧ occM D B s0.memory US I0 ≠ some 0) ?_)
    (fun _ _ _ ⟨a,b,c⟩ => ⟨⟨a,b⟩,c⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  intro ⟨hI0,hocc⟩
  have hn1 : 1 ≤ N.toNat := by
    by_contra h
    have z := hashOccupiedCount_zero_reads C (hashOccupancyRead s0 US) (by rw [← inv.agreement]; omega) I0 hI0
    rw [← occE] at z
    exact hocc z
  obtain ⟨DP,hDP,hdp⟩ := oi.1 I0 hI0 (by rw [← occE]; exact hocc)
  refine aqgd_decD (Pb := fun L M _ => LK [(ofString "deleted_pos",DP),(ofString "order_pos",OPS),(ofString "order",OS),
      (ofString "used",US),(ofString "vals",VS),(ofString "keys",KS),(ofString "stride",SD),(ofString "klen",KL),
      (ofString "cap",C),(ofString "i",I0),(ofString "key",Kk),(ofString "t",T)] L ∧ M = s0.memory)
    (Qb := fun _ _ _ => True) _ _ _ (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ _ _ => trivial)
  · intro F s v H _ _ _ ⟨hl,hm⟩ _ ev _
    have hops := lk_get hl (ofString "order_pos") OPS (by simp)
    have hi := lk_get hl (ofString "i") I0 (by simp)
    have e := ev_load_at s _ _ (eval_delScaled8 s _ _ OPS I0 hops hi) v ev
    rw [hm,hDP] at e; subst e
    exact ⟨lk_cons hl _ _ (by lkne),hm⟩
  refine aqgd_decD (Pb := DLI D B s0.memory T Kk KL SD C N KS VS US OS OPS DP)
    (Qb := fun _ _ _ => True) _ _ _ (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ _ _ => trivial)
  · intro F s v H _ _ _ ⟨hl,hm⟩ _ ev _
    have := ev_var s _ _ (lk_get hl (ofString "i") I0 (by simp)) _ ev; subst this
    refine ⟨I0,I0,lk_sub (lk_cons hl _ _ (by lkne)) ?_,hI0,hI0,?_⟩
    · intro p hp
      simp only [dL,dB,List.mem_cons,List.not_mem_nil,or_false] at hp ⊢
      rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h]
    · rw [hm]
      exact ⟨fun _ _ => rfl,fun q hq ho => oi.1 q hq (by rw [← occE]; exact ho),oi.2,hdr⟩
  exact aqgd_seq (aqgd_whileBreak (C := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => trivial) (del_body rg room.le hw))
    (del_tail rg room.le hn1 hdp hw)

#print axioms del_aqgd
end main

theorem kl_le {T KL SD C KS VS US OS OPS : BitVec 64} {b : Nat} (rg : DReg T KL SD C KS VS US OS OPS b) :
    KL.toNat ≤ 33806089496 := by
  have kb := rg.kb; have ub := rg.ub; have ob := rg.ob; have eb := rg.eb; have fits := rg.fits
  have c1 : 1 ≤ C.toNat := by rw [rg.pow]; exact Nat.one_le_two_pow
  have : SD.toNat ≤ C.toNat * SD.toNat := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- A returned original `htab_del` body run keeps the content invariant with the count kept or decremented, and
changes memory only inside the table (the aligned-world contract replayed with a larger clock). -/
theorem del_content {F : Type} (r post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) (T Kk : BitVec 64)
    (l : TLay) (D : BitVec 64 → Prop) (B : Bool) (hd : r.memaddrs = D) (hb : r.be = B)
    (code : r.code = originalRuntimeCode)
    (ht : r.locals.lookup (ofString "t") = some (.val (.word T)))
    (hk : r.locals.lookup (ofString "key") = some (.val (.word Kk)))
    (tc : TCont D B r.memory T l) (room : l.N.toNat < l.C.toNat)
    (run : evaluateHOLFiniteState r (sourceFunctionBody Guest.guestFn_htab_del) = (some (.returned v),post)) :
    ∃ N' : BitVec 64, (N' = l.N ∨ N'.toNat + 1 = l.N.toNat) ∧
      TCont D B post.memory T ⟨l.KL,l.SD,l.C,N',l.KS,l.VS,l.US,l.OS,l.OPS,l.b⟩ ∧
      ∀ x, ¬ InTabF T l.KS l.SD l.C l.US l.VS l.OS l.OPS x → post.memory x = r.memory x := by
  obtain ⟨inv,oi⟩ := tc.toState r rfl hd hb code
  have run' := panPropsEvaluateAddClockEq (sourceFunctionBody Guest.guestFn_htab_del) r _ post
    (delBodyCost l.KL l.C) ⟨run,by simp⟩
  have meta' := evaluateHOLFiniteState_metadata r (sourceFunctionBody Guest.guestFn_htab_del)
  rw [run] at meta'
  obtain ⟨N',hN',inv2,oi2,_,_,fr⟩ := htabDel_returned_fine
    { r with clock := r.clock + delBodyCost l.KL l.C } _ v l.KL T l.KS l.SD l.C l.US l.VS l.OS l.OPS l.N Kk l.b
    (inv.transfer rfl rfl rfl rfl) (oi.transfer rfl rfl rfl) ht hk room (kl_le (dreg_of_aligned inv)) (by simp) run'
  refine ⟨N',hN',⟨F,{ post with clock := post.clock + delBodyCost l.KL l.C },rfl,
    (by have := meta'.2.1; dsimp only at this; exact this.trans hd),
    (by have := meta'.2.2.1; dsimp only at this; exact this.trans hb),
    (by have := meta'.1; dsimp only at this; exact this.trans code),inv2,oi2⟩,fun x hx => fr x hx⟩

#print axioms del_content

section full
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64}

/-- The original `htab_del` body on a table with content invariant `TCont` and `count < capacity`: every outcome
keeps the watched word `w` outside the table's header and arrays; a returned run leaves `TCont` with the count kept
or decremented and changes memory only inside the table. -/
theorem del_aqgd_content {M0 : Mem} {T : BitVec 64} {l : TLay} (Kk : BitVec 64) (tc : TCont D B M0 T l)
    (room : l.N.toNat < l.C.toNat) (hw : ¬ InTabF T l.KS l.SD l.C l.US l.VS l.OS l.OPS w) :
    AQGD D B A w (fun _ => True) (fun L M _ => LK [(ofString "key",Kk),(ofString "t",T)] L ∧ M = M0)
      (fun _ _ _ => True)
      (fun _ M _ => ∃ N' : BitVec 64, (N' = l.N ∨ N'.toNat + 1 = l.N.toNat) ∧
        TCont D B M T ⟨l.KL,l.SD,l.C,N',l.KS,l.VS,l.US,l.OS,l.OPS,l.b⟩ ∧
        ∀ x, ¬ InTabF T l.KS l.SD l.C l.US l.VS l.OS l.OPS x → M x = M0 x)
      (sourceFunctionBody Guest.guestFn_htab_del) := by
  obtain ⟨F0,s0,sm,sd,sb,_,inv,oi⟩ := tc
  subst sm
  refine aqgd_conseq (aqgd_augment (del_aqgd (A := A) s0 Kk inv oi sd sb room hw) ?_) (fun _ _ _ h => h)
    (fun _ _ _ h => h) (fun _ _ _ h => h.2)
  intro F s code dom ⟨hl,hm⟩ v post run
  have ht := lk_get hl (ofString "t") T (by simp)
  have hk := lk_get hl (ofString "key") Kk (by simp)
  obtain ⟨N',hN',tc',fr⟩ := del_content s post v T Kk l D B dom.2.1 dom.2.2 code ht hk
    ⟨F0,s0,hm.symm,sd,sb,inv.code,inv,oi⟩ room run
  exact ⟨N',hN',tc',fun x hx => (fr x hx).trans (congrFun hm x)⟩

#print axioms del_aqgd_content
end full
end InitECandidate.Runtime
