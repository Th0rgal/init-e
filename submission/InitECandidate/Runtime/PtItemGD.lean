import InitECandidate.Runtime.PtFamGD
/-!
The actual `var {1,1,1} s = htab_item(t, i)` on a table with content (`TCont`: aligned layout and order invariant) and
`i` below its count: the call is read-only and returns `(b, keys + slot * stride, v)` with `slot < capacity`. Keys of
such items are 8-aligned and (for key length at least 20) end at least 52 bytes below the heap bound, as root's
`htab_get`/`htab_set` contracts need.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem itm_toNat_add_mul8 (a i : BitVec 64) (h : a.toNat + i.toNat * 8 < 2 ^ 64) :
    (a + i * 8).toNat = a.toNat + i.toNat * 8 := by
  rw [BitVec.toNat_add,BitVec.toNat_mul]; simp; omega

theorem itm_toNat_add_mul (a i k : BitVec 64) (h : a.toNat + i.toNat * k.toNat < 2 ^ 64) :
    (a + i * k).toNat = a.toNat + i.toNat * k.toNat := by
  have : i.toNat * k.toNat < 2 ^ 64 := by omega
  rw [BitVec.toNat_add,BitVec.toNat_mul,Nat.mod_eq_of_lt this]; omega

/-- A key of an item of an aligned table (key length at least 20, capacity at least 2) is aligned and bounded. -/
theorem item_key_ok {F : Type} {s : PanSemStateFiniteExact 64 F} {KL Tt KS SD C US VS OS OPS N slot : BitVec 64}
    {b : Nat} (inv : HtabAligned KL Tt KS SD C US VS OS OPS N b s) (hKL : 20 ≤ KL.toNat) (hC : 2 ≤ C.toNat)
    (hs : slot.toNat < C.toNat) :
    (KS + slot * SD).toNat % 8 = 0 ∧ (KS + slot * SD).toNat + 52 ≤ 33806089496 := by
  have k1 := inv.keysBefore; have k3 := inv.usedBefore; have k4 := inv.orderBefore; have k5 := inv.endBound
  have fi := inv.fits; have sa := inv.strideAligned; have ka := inv.keysAligned
  have m : (slot.toNat + 1) * SD.toNat ≤ C.toNat * SD.toNat := Nat.mul_le_mul_right _ hs
  rw [Nat.succ_mul] at m
  have e := itm_toNat_add_mul KS slot SD (by omega)
  rw [e]
  refine ⟨?_,by omega⟩
  have := Nat.mul_mod slot.toNat SD.toNat 8
  rw [sa] at this; simp at this; omega

/-- A returned run of the actual `htab_item` body on a `TCont` table at an ordinal below the count. -/
theorem tcont_item_ret {F : Type} {D : BitVec 64 → Prop} {B : Bool} (s post : PanSemStateFiniteExact 64 F)
    (w : ValueHOL 64) (Tt I : BitVec 64) (l : TLay) (tc : TCont D B s.memory Tt l) (hd : s.memaddrs = D)
    (hb : s.be = B) (code : s.code = originalRuntimeCode)
    (tL : s.locals.lookup (ofString "t") = some (.val (.word Tt)))
    (oL : s.locals.lookup (ofString "ordinal") = some (.val (.word I)))
    (hI : I.toNat < l.N.toNat) (hNC : l.N.toNat < l.C.toNat)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_htab_item) = (some (.returned w),post)) :
    ∃ b slot vv : BitVec 64, slot.toNat < l.C.toNat ∧ s.memory (l.OS + I * 8) = .word slot ∧
      s.memory (l.VS + slot * 8) = .word vv ∧
      w = .rStruct [.val (.word b),.val (.word (l.KS + slot * l.SD)),.val (.word vv)] := by
  obtain ⟨inv,oi⟩ := tc.toState s rfl hd hb code
  obtain ⟨slot,cO,sl⟩ := oi.2 I hI
  have hk := inv.headerKeys; have hv := inv.headerValues; have k1 := inv.keysBefore; have k2 := inv.valuesBefore
  have k3 := inv.usedBefore; have k4 := inv.orderBefore; have k5 := inv.endBound
  have ta := inv.tableAligned; have oa := inv.orderAligned; have va := inv.valuesAligned
  have dom : ∀ a : BitVec 64, a.toNat % 8 = 0 → Tt.toNat ≤ a.toNat →
      a.toNat < l.OPS.toNat + l.C.toNat * 8 → s.memaddrs a := inv.domain
  have eo : ∀ o : Nat, o < 72 → (Tt + BitVec.ofNat 64 o).toNat = Tt.toNat + o := fun o ho => by
    rw [BitVec.toNat_add]; simp; omega
  have hdr : ∀ o : Nat, o < 72 → o % 8 = 0 → s.memaddrs (Tt + BitVec.ofNat 64 o) := fun o ho h8 =>
    dom _ (by rw [eo o ho]; omega) (by rw [eo o ho]; omega) (by rw [eo o ho]; omega)
  have eOrd := itm_toNat_add_mul8 l.OS I (by omega)
  have eVal := itm_toNat_add_mul8 l.VS slot (by omega)
  have dOrd : s.memaddrs (l.OS + I * 8) := dom _ (by rw [eOrd]; omega) (by rw [eOrd]; omega) (by rw [eOrd]; omega)
  have dVal : s.memaddrs (l.VS + slot * 8) := dom _ (by rw [eVal]; omega) (by rw [eVal]; omega) (by rw [eVal]; omega)
  cases hvv : s.memory (l.VS + slot * 8) with
  | word vv =>
    obtain ⟨b,e⟩ := htabItem_returned s post w Tt I l.OS slot l.KS l.SD l.VS vv code tL oL (hdr 56 (by omega) rfl)
      inv.cell56 dOrd cO (hdr 32 (by omega) rfl) inv.cell32 (hdr 8 (by omega) rfl) inv.cell8 (hdr 40 (by omega) rfl)
      inv.cell40 dVal hvv run
    exact ⟨b,slot,vv,sl,cO,hvv,e⟩

#print axioms tcont_item_ret

section ti
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {Vn : MlS → Prop} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64}

/-- The actual `var {1,1,1} name = htab_item(t, i)` on a `TCont` table at an ordinal below the count: read-only, the
continuation gets `name = (b, keys + slot * stride, v)` with `slot < capacity`. -/
theorem aqgd_decCall_htabItem_tc {LP : GA → Prop} {Pc Qc Q : GA → Mem → GA → Prop} (name : MlS) (et ei : ExpHOL 64)
    {cont : ProgHOL 64} (Tt I : BitVec 64) (l : TLay) (M1 : Mem) (G1 : GA)
    (tc : TCont D B M1 Tt l) (hI : I.toNat < l.N.toNat) (hNC : l.N.toNat < l.C.toNat)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.memaddrs = D → s.memory = M1 → s.globals = G1 →
      LP s.locals → evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [et,ei] =
        some [.val (.word Tt),.val (.word I)])
    (hshape : Vn name → ShapeHOL.comb [.one,.one,.one] = .one)
    (hres : ∀ (L : GA) (b slot vv : BitVec 64), LP L → slot.toNat < l.C.toNat →
      M1 (l.OS + I * 8) = .word slot → M1 (l.VS + slot * 8) = .word vv →
      Pc (L.update (name,.rStruct [.val (.word b),.val (.word (l.KS + slot * l.SD)),.val (.word vv)])) M1 G1)
    (hc : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w Vn Pc Qc RR cont)
    (hq : ∀ (L L' : GA) (M' : Mem) (G' : GA), LP L → Qc L' M' G' → Q (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w Vn (fun L M G => LP L ∧ M = M1 ∧ G = G1) Q RR
      (.decCall name (.comb [.one,.one,.one]) (ofString "htab_item") [et,ei] cont) := by
  refine aqgd_decCallSpecD (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' L M G => (L.lookup (ofString "t") = some (.val (.word Tt)) ∧
      L.lookup (ofString "ordinal") = some (.val (.word I))) ∧ M = M0' ∧ G = G0')
    (RRe := fun _ M0' G0' v M' G' => (M' = M0' ∧ G' = G0') ∧ ∃ b slot vv : BitVec 64, slot.toNat < l.C.toNat ∧
      M0' (l.OS + I * 8) = .word slot ∧ M0' (l.VS + slot * 8) = .word vv ∧
      v = .rStruct [.val (.word b),.val (.word (l.KS + slot * l.SD)),.val (.word vv)])
    (Pc := Pc) (Qc := Qc) _ _ _ _ _ _ _ originalRuntimeCode_htabItem_lookup (by simp) ?_ ?_ hshape ?_ hc ?_
  · intro L0 M0' G0' ⟨_,hM,_⟩
    have tc' : TCont D B M0' Tt l := by rw [hM]; exact tc
    refine aqgd_addReturn (aqgd_conseq (aqgd_of_mf htabItem_memoryFrame (by body_check Guest.guestFn_htab_item)
      (by body_check Guest.guestFn_htab_item) M0' G0') (fun _ _ _ h => h.2) (fun _ _ _ _ => trivial)
      (fun _ _ _ h => h)) ?_
    intro F s code dom _ _ ⟨⟨tl,ol⟩,sm,_⟩ v post run
    obtain ⟨b,slot,vv,sl,c1,c2,e⟩ := tcont_item_ret s post v Tt I l (by rw [sm]; exact tc') dom.2.1 dom.2.2 code tl ol
      hI hNC run
    exact ⟨b,slot,vv,sl,by rw [← sm]; exact c1,by rw [← sm]; exact c2,e⟩
  · intro F s values callee rs _ dom H hG ⟨lp,hM,hG1⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [hargs s dom hM hG1 lp] at args
    simp only [Option.some.injEq] at args
    subst args
    rw [pan_two_word_lookup_shape _ _ (ofString "t") (ofString "ordinal") _ _ _ _ (by decide)
      originalRuntimeCode_htabItem_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
      by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,hM,hG⟩ ⟨⟨eM,eG⟩,b,slot,vv,sl,c1,c2,ev⟩ _
    rw [eM,eG,hM,hG,ev]
    rw [hM] at c1 c2
    exact hres L b slot vv lp sl c1 c2
  · intro L M G L' M' G' ⟨lp,_,_⟩ qc
    exact hq L L' M' G' lp qc

#print axioms aqgd_decCall_htabItem_tc
end ti
end InitECandidate.Runtime
