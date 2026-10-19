import InitECandidate.Runtime.HtabMergeTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-! The storage loop with layout clamps instead of growth tracking: every laid table has
orderPos + cap*8 ≤ limit, so capacities (and counts) are at most limit/8 = 4225761187 at every point.
With the bound constants set to limit/8 (`MergeCtx.BoundsK`), no premise grows with n·NS; the per-call
costs are uniform constants (`unionCostK`, `iterCostK`). -/

set_option maxHeartbeats 4000000 in
/-- `htab_set(bouter, key, b)` with a registered inner table b: the block map stays valid with its values in
the registry, its block is kept or moves above the heap pointer, and the inner tables and outer footprint
are untouched. -/
theorem MergeCtx.CoreW.after_setK {c : MergeCtx} (st : c.Static) {IB II : Nat} {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (p : BitVec 64) (R : Set (BitVec 64)) (Z : BitVec 64 → Nat × Nat)
    (core : c.CoreW IB II s p R Z) (tableArgument keyArgument valueArgument : ExpHOL 64) (key b : BitVec 64)
    (member : b ∈ R)
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word c.BO),.val (.word key),.val (.word b)])
    (hCB : 4225761187 ≤ c.CB) (hNB : 4225761187 ≤ c.NB0) (budget : c.setCost ≤ s.clock)
    (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "htab_set")
      [tableArgument,keyArgument,valueArgument]) = (none,post)) :
    ∃ p' : BitVec 64, c.CoreW (IB + 1) II post p' R Z ∧ post.locals = s.locals := by
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,⟨bc,bk,bu,bv,bo,bp,bn,bb,binv,bt,br,bvt,btop,bnb,bcb,bz⟩,⟨ii,io,ip⟩⟩ := core
  have ofB := st.ofBelow
  have bzB := MergeCtx.Bouter.zone_below bc bk bu bv bo bp bn bb binv btop
  have zoneR : ∀ b ∈ R, ∀ w, TZone b (Z b).1 (Z b).2 w → w < p.toNat := fun b mem w h => (ii b mem).zone_below w h
  have hdr : c.BO.toNat + 72 ≤ p.toNat := by
    have := bzB c.BO.toNat (Or.inl ⟨le_refl _,by omega⟩); have := binv.headerKeys; have := binv.keysBefore
    have := binv.usedBefore; have := binv.orderBefore; omega
  have arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → c.BO.toNat ≤ a.toNat → a.toNat < 33806089496 → s.memaddrs a :=
    fun a h1 h2 h3 => by rw [a2]; exact st.arena a h1 (by have := st.LB; omega) h3
  have bud : setBodyCost c.KB bc bn + 1 ≤ s.clock := by
    have := setBodyCost_mono c.KB bc (BitVec.ofNat 64 c.CB) bn (BitVec.ofNat 64 c.CB)
      (by rw [ofNat_toNat_small _ (by have := st.cbSmall; omega)]; omega)
      (by rw [ofNat_toNat_small _ (by have := st.cbSmall; omega)]; omega)
      (by rw [ofNat_toNat_small _ (by have := st.cbSmall; omega)]; have := st.cbSmall; omega)
    unfold MergeCtx.setCost at budget; omega
  obtain ⟨⟨c',k',u',v',o',op',n',b',lo',hi',laid',tables',counts,capB',loB'⟩,locals,maddrs,mbe,frame⟩ :=
    htabSet_call_normal_laidTop s post _ _ _ c.KB c.BO bk c.SB bc bu bv bo bp bn key b p bb
      (min bk.toNat bv.toNat) (bp.toNat + bc.toNat * 8) (Or.inl ⟨binv,rfl,rfl⟩) args a5 a7 hdr a8 arena bt br
      st.kbSmall bud run
  obtain ⟨⟨c2,k2,u2,v2,o2,op2,n2,b2,inv2,_,tables2,vt2⟩,_,_,_⟩ :=
    htabSet_call_normal_vtabs s post _ _ _ c.KB c.BO bk c.SB bc bu bv bo bp bn key b p bb binv args a5 a7 hdr a8 arena
      bt br st.kbSmall R bvt member btop bud run
  -- both contracts describe the same post table
  have e : ∀ {x y : BitVec 64} {q : HolWordLab 64}, q = .word x → q = .word y → y = x := by
    intro x y q hx hy; rw [hx] at hy; cases hy; rfl
  rcases laid' with ⟨inv',rfl,rfl⟩ | ⟨d,rfl,rfl⟩
  · obtain ⟨ek,ec,eu,ev,eo,eop,en,eb⟩ := inv'.unique inv2
    subst ek; subst ec; subst eu; subst ev; subst eo; subst eop; subst en; subst eb
    have rel := normalRel_apply (htabSet_call_normalRel [tableArgument,keyArgument,valueArgument]) (X := s)
      (by rw [run]; exact Or.inl rfl) a1
    rw [run] at rel
    obtain ⟨p',hp',pp',pal',pin2⟩ := rel.2 p a5 a7 a8
    have postCode : post.code = originalRuntimeCode := inv2.code
    have keep : ∀ w : BitVec 64, w.toNat < p.toNat → ¬ TZone c.BO (min bk.toNat bv.toNat) (bp.toNat + bc.toNat * 8) w.toNat →
        post.memory w = s.memory w := by
      intro w lt nz
      unfold TZone at nz
      exact frame w lt (by omega) (by omega)
    have newTop : bp.toNat + bc.toNat * 8 ≤ p.toNat → op2.toNat + c2.toNat * 8 ≤ p'.toNat := by
      intro _
      rcases loB' with ⟨_,hh⟩ | ⟨_,p3,hp3,le3⟩
      · omega
      · rw [hp'] at hp3; simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at hp3; subst hp3; exact le3
    refine ⟨p',⟨postCode,maddrs.trans a2,mbe.trans a3,fun w h => by
        rw [keep w (by have := ofB _ h; omega) (fun hz => (bz _ hz).1 h)]; exact a4 w h,
      hp',by omega,pal',pin2,heapRel_preorder.trans _ _ _ a9 rel,?_,?_⟩,locals⟩
    have roomK : n2.toNat < c2.toNat := by rcases counts with ⟨rfl,rfl⟩ | ⟨h1,h2⟩ <;> omega
    have capK : c2.toNat ≤ 4225761187 := by have := inv2.endBound; omega
    · refine ⟨c2,k2,u2,v2,o2,op2,n2,b2,inv2,tables',?_,vt2,newTop btop,?_,?_,?_⟩
      · exact roomK
      · omega
      · omega
      · intro w hz
        rcases loB' with ⟨hl,hh⟩ | ⟨lp,_⟩
        · rw [hl,hh] at hz; exact bz w hz
        · refine ⟨fun hf => ?_,fun b mem hb => ?_⟩
          · have := ofB w hf
            unfold TZone at hz
            rcases hz with hz | hz
            · exact (bz w (Or.inl hz)).1 hf
            · omega
          · have := zoneR b mem w hb
            unfold TZone at hz
            rcases hz with hz | hz
            · exact (bz w (Or.inl hz)).2 b mem hb
            · omega
    · refine ⟨fun b mem => (ii b mem).congr maddrs mbe (postCode.trans (ii b mem).code.symm)
        (fun w hw => keep w (zoneR b mem w.toNat hw) (fun hz => (bz _ hz).2 b mem hw)) (by omega),io,ip⟩
  · exfalso
    have ck := congrArg BitVec.toNat (e d.cell32 inv2.cell32)
    have := d.keysBelow; have := inv2.headerKeys
    have : k'.toNat ≤ k'.toNat + c'.toNat * c.SB.toNat := Nat.le_add_right _ _
    omega

#print axioms MergeCtx.CoreW.after_setK

/-- A uniform union-call bound from layout clamps: destination capacity and count at most limit/8 and a
source count at most NS ≤ limit/8. -/
def MergeCtx.unionCostK (c : MergeCtx) : Nat :=
  c.NS * (1 + 1 + ((setBodyCost c.KI (BitVec.ofNat 64 (4 * (4225761187 + c.NS))) (BitVec.ofNat 64 (4225761187 + c.NS))
    + 1) + 0) + 1) + 1

theorem MergeCtx.unionCostK_mono (c : MergeCtx) (hNS : c.NS ≤ 4225761187)
    {F : Type} (dst stride src sn skeys sstride svals sorder count0 cap0 p : BitVec 64)
    (lo hi : Nat) (s : PanSemStateFiniteExact 64 F) (hc : cap0.toNat ≤ 4225761187) (hn : count0.toNat ≤ 4225761187)
    (hs : sn.toNat ≤ c.NS) :
    sn.toNat * ((unionCtxOf c.KI dst stride src sn skeys sstride svals sorder count0 cap0 p lo hi s).stepCost + 1) + 1 ≤
      c.unionCostK := by
  have m := setBodyCost_mono c.KI
    (BitVec.ofNat 64 (unionCtxOf c.KI dst stride src sn skeys sstride svals sorder count0 cap0 p lo hi s).capMax)
    (BitVec.ofNat 64 (4 * (4225761187 + c.NS)))
    (BitVec.ofNat 64 (count0.toNat + sn.toNat)) (BitVec.ofNat 64 (4225761187 + c.NS))
    (by
      rw [ofNat_toNat_small _ (by unfold UnionCtx.capMax unionCtxOf; simp only; omega),
        ofNat_toNat_small _ (by omega)]
      unfold UnionCtx.capMax unionCtxOf; simp only; omega)
    (by rw [ofNat_toNat_small _ (by omega),ofNat_toNat_small _ (by omega)]; omega)
    (by rw [ofNat_toNat_small _ (by omega)]; omega)
  unfold MergeCtx.unionCostK UnionCtx.stepCost
  change sn.toNat * (1 + 1 + ((setBodyCost c.KI _ (BitVec.ofNat 64 (count0.toNat + sn.toNat)) + 1) + 0) + 1) + 1 ≤ _
  have := Nat.mul_le_mul hs (show 1 + 1 + ((setBodyCost c.KI
      (BitVec.ofNat 64 (unionCtxOf c.KI dst stride src sn skeys sstride svals sorder count0 cap0 p lo hi s).capMax)
      (BitVec.ofNat 64 (count0.toNat + sn.toNat)) + 1) + 0) + 1 ≤ 1 + 1 + ((setBodyCost c.KI
      (BitVec.ofNat 64 (4 * (4225761187 + c.NS))) (BitVec.ofNat 64 (4225761187 + c.NS)) + 1) + 0) + 1 by omega)
  omega

#print axioms MergeCtx.unionCostK_mono

set_option maxHeartbeats 4000000 in
/-- `htab_union_into(b, src)` with a registered inner table b and an outer-side source table: b stays a
valid inner table (block kept or moved above the heap pointer), everything else is untouched. -/
theorem MergeCtx.CoreW.after_unionK {c : MergeCtx} (st : c.Static) (hNS : c.NS ≤ 4225761187)
    {IB II : Nat} {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (p : BitVec 64) (R : Set (BitVec 64)) (Z : BitVec 64 → Nat × Nat)
    (core : c.CoreW IB II s p R Z) (dstArgument srcArgument : ExpHOL 64) (b : BitVec 64) (member : b ∈ R)
    (src sKeyLength skeys sstride scapacity sused svalues sorder sorderPos sn : BitVec 64) (sbits : Nat)
    (sinv : HtabRegions sKeyLength src skeys sstride scapacity sused svalues sorder sorderPos sn sbits s)
    (stables : OrderInv s scapacity sn sused sorder sorderPos) (snBound : sn.toNat ≤ c.NS)
    (srcFoot : ∀ w, ((src.toNat ≤ w ∧ w < src.toNat + 72) ∨
      (sorder.toNat ≤ w ∧ w < sorder.toNat + scapacity.toNat * 8) ∨
      (svalues.toNat ≤ w ∧ w < svalues.toNat + scapacity.toNat * 8)) → c.OFoot w)
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [dstArgument,srcArgument] =
      some [.val (.word b),.val (.word src)])
    (hCI : 4225761187 ≤ c.CI) (hNI : 4225761187 ≤ c.NI0) (budget : c.unionCostK ≤ s.clock)
    (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "htab_union_into") [dstArgument,srcArgument]) =
      (none,post)) :
    ∃ (p' : BitVec 64) (Z' : BitVec 64 → Nat × Nat), c.CoreW IB (II + 1) post p' R Z' ∧ post.locals = s.locals ∧
      s.clock ≤ post.clock + c.unionCostK ∧ ∀ b' ∈ R, b' ≠ b → Z' b' = Z b' := by
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,⟨bc,bk,bu,bv,bo,bp,bn,bb,binv,bt,br,bvt,btop,bnb,bcb,bz⟩,⟨ii,io,ip⟩⟩ := core
  have ofB := st.ofBelow
  have bzB := MergeCtx.Bouter.zone_below bc bk bu bv bo bp bn bb binv btop
  have zoneR : ∀ b ∈ R, ∀ w, TZone b (Z b).1 (Z b).2 w → w < p.toNat := fun b mem w h => (ii b mem).zone_below w h
  obtain ⟨cap0,keys0,stride0,used0,vals0,order0,op0,count0,bits0,laid,tables,room,hTop,hL,hN,hC⟩ := ii b member
  have hdrLe := laid.header_le_hi
  have cap0K : cap0.toNat ≤ 4225761187 := by have := laid.regions.endBound; omega
  have bud := c.unionCostK_mono hNS b stride0 src sn skeys sstride svalues sorder count0 cap0 p
    (Z b).1 (Z b).2 s cap0K (by omega) snBound
  obtain ⟨D,⟨⟨p',hp',pp',pal',pin'⟩,rel⟩,L,A,Be,C,Fr,Clk⟩ := htabUnionInto_tables_callT s post _ _ c.KI b keys0 stride0
    cap0 used0 vals0 order0 op0 count0 bits0 (Z b).1 (Z b).2 laid tables room src sKeyLength skeys sstride scapacity
    sused svalues sorder sorderPos sn sbits sinv stables args p a5 a7 a8 (by omega)
    (fun a h1 h2 h3 => by rw [a2]; exact st.arena a h1 (by omega) h3) (by rw [st.kI]; decide)
    (fun w h => by
      have hf := srcFoot _ h
      have := ofB _ hf
      have nz := io b member w.toNat
      unfold TZone at nz
      refine ⟨by omega,?_,?_⟩
      · by_cases x : b.toNat ≤ w.toNat
        · right; by_contra y; exact nz (Or.inl ⟨x,by omega⟩) hf
        · left; omega
      · by_cases x : (Z b).1 ≤ w.toNat
        · right; by_contra y; exact nz (Or.inr ⟨x,by omega⟩) hf
        · left; omega)
    (by omega) run
  change p.toNat ≤ p'.toNat at pp'
  obtain ⟨c',k',u',v',o',op',n',b',lo',hi',laid',tables',room',lb,ub,capB,top⟩ := D
  have postCode : post.code = originalRuntimeCode := C.trans a1
  -- what the union keeps: below p, outside b's zone
  have keep : ∀ w : BitVec 64, w.toNat < p.toNat → ¬ TZone b (Z b).1 (Z b).2 w.toNat → post.memory w = s.memory w := by
    intro w lt nz
    unfold TZone at nz
    refine Fr w (show w.toNat < p.toNat ∧ (w.toNat < b.toNat ∨ b.toNat + 72 ≤ w.toNat) ∧
      (w.toNat < (Z b).1 ∨ (Z b).2 ≤ w.toNat) from ⟨lt,?_,?_⟩)
    · by_cases x : b.toNat ≤ w.toNat
      · right; by_contra y; exact nz (Or.inl ⟨x,by omega⟩)
      · left; omega
    · by_cases x : (Z b).1 ≤ w.toNat
      · right; by_contra y; exact nz (Or.inr ⟨x,by omega⟩)
      · left; omega
  let Z' : BitVec 64 → Nat × Nat := fun x => if x = b then (lo',hi') else Z x
  have zO : ∀ x, x ≠ b → Z' x = Z x := fun x ne => by simp [Z',ne]
  have zB : Z' b = (lo',hi') := by simp [Z']
  -- the new zone of b: the old one, or its header plus a block at or above p
  have newZone : ∀ w, TZone b lo' hi' w → TZone b (Z b).1 (Z b).2 w ∨ p.toNat ≤ w := by
    intro w h
    rcases top with ⟨hl,hh⟩ | ⟨lp,_⟩
    · left; rw [hl,hh] at h; exact h
    · unfold TZone at h
      rcases h with h | h
      · left; exact Or.inl h
      · right; change p.toNat ≤ lo' at lp; omega
  -- the block map is untouched
  have bKeep : ∀ w : BitVec 64, w.toNat < bp.toNat + bc.toNat * 8 →
      TZone c.BO (min bk.toNat bv.toNat) (bp.toNat + bc.toNat * 8) w.toNat → post.memory w = s.memory w :=
    fun w lt hz => keep w (by omega) ((bz _ hz).2 b member)
  have bFoot : ∀ w : BitVec 64, HtabFoot c.BO bc bu bo bp w.toNat → post.memory w = s.memory w := by
    intro w h
    have lt := binv.foot_below w.toNat h
    refine bKeep w lt ?_
    have := (show HtabLaid c.KB c.BO bk c.SB bc bu bv bo bp bn bb (min bk.toNat bv.toNat) (bp.toNat + bc.toNat * 8) s
      from Or.inl ⟨binv,rfl,rfl⟩).foot_sub w.toNat h
    exact this
  have K := binv.toRegions.foot_keep (r := post) bFoot
  have binv' := binv.congr A Be (postCode.trans binv.code.symm) K.1 K.2.1
  have bt' := bt.congr binv.toRegions.count_le A Be K.2.1 K.2.2.1 K.2.2.2
  have bvt' := bvt.congr binv bt A Be (fun w h => bKeep w h.2 (Or.inr h))
  refine ⟨p',Z',⟨postCode,A.trans a2,Be.trans a3,fun w h => by
      rw [keep w (by have := ofB _ h; omega) (fun hz => io b member _ hz h)]; exact a4 w h,
      hp',by omega,pal',pin',heapRel_preorder.trans _ _ _ a9 rel,?_,?_⟩,L,by omega,fun b' mem ne => zO b' ne⟩
  · refine ⟨bc,bk,bu,bv,bo,bp,bn,bb,binv',bt',br,bvt',by omega,bnb,bcb,fun w hz => ⟨(bz w hz).1,fun b2 mem hb => ?_⟩⟩
    by_cases e : b2 = b
    · subst e
      rw [zB] at hb
      rcases newZone w hb with old | hi
      · exact (bz w hz).2 b2 mem old
      · have := bzB w hz; omega
    · rw [zO b2 e] at hb; exact (bz w hz).2 b2 mem hb
  · refine ⟨fun b2 mem => ?_,fun b2 mem w h => ?_,fun b2 m2 b3 m3 ne w h h' => ?_⟩
    · by_cases e : b2 = b
      · subst e
        rw [zB]
        refine ⟨c',k',stride0,u',v',o',op',n',b',laid',tables',room',?_,hL,?_,?_⟩
        · rcases top with ⟨_,hh⟩ | ⟨_,p3,hp3,le3⟩
          · change hi' = (Z b2).2 at hh; omega
          · change post.globals.lookup _ = _ at hp3
            rw [hp'] at hp3
            simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at hp3
            subst hp3; exact le3
        · have := laid'.regions.endBound
          have : c.NI0 ≤ c.NI0 + (II + 1) * c.NS := Nat.le_add_right _ _
          change n'.toNat < c'.toNat at room'
          omega
        · have := laid'.regions.endBound; omega
      · rw [zO b2 e]
        refine ((ii b2 mem).congr A Be (postCode.trans (ii b2 mem).code.symm) (fun w hw => keep w
          (zoneR b2 mem w.toNat hw) (fun hb => ip b member b2 mem (Ne.symm e) w.toNat ?_ ?_)) (by omega)).mono
          (by rw [Nat.add_mul,Nat.one_mul]; omega)
        · exact hb
        · exact hw
    · by_cases e : b2 = b
      · subst e
        rw [zB] at h
        rcases newZone w h with old | hi
        · exact io b2 mem w old
        · intro hf; have := ofB w hf; omega
      · rw [zO b2 e] at h; exact io b2 mem w h
    · by_cases e2 : b2 = b
      · subst e2
        rw [zB] at h; rw [zO b3 (Ne.symm ne)] at h'
        rcases newZone w h with old | hi
        · exact ip b2 m2 b3 m3 ne w old h'
        · have := zoneR b3 m3 w h'; omega
      · by_cases e3 : b3 = b
        · subst e3
          rw [zB] at h'; rw [zO b2 e2] at h
          rcases newZone w h' with old | hi
          · exact ip b2 m2 b3 m3 ne w h old
          · have := zoneR b2 m2 w h; omega
        · rw [zO b2 e2] at h; rw [zO b3 e3] at h'; exact ip b2 m2 b3 m3 ne w h h'

#print axioms MergeCtx.CoreW.after_unionK

set_option maxHeartbeats 4000000 in
/-- The choice of the inner table: a fresh registered table stored into the block map on a miss, the found
registered table on a hit. -/
theorem merge_chooseK {c : MergeCtx} (st : c.Static) {IB II : Nat} {F : Type} (Y : PanSemStateFiniteExact 64 F)
    (p : BitVec 64) (R : Set (BitVec 64)) (Z : BitVec 64 → Nat × Nat) (core : c.CoreW IB II Y p R Z)
    (f mv b0 kp v : BitVec 64)
    (mL : Y.locals.lookup (ofString "m") = some (.rStruct [.val (.word f),.val (.word mv)]))
    (sL : Y.locals.lookup (ofString "s") = some (.rStruct [.val (.word b0),.val (.word kp),.val (.word v)]))
    (boL : Y.locals.lookup (ofString "bouter") = some (.val (.word c.BO)))
    (binL : Y.locals.lookup (ofString "binner") = some (.val (.word 0)))
    (hit : f = 0 ∨ mv ∈ R) (hCB : 4225761187 ≤ c.CB) (hNB : 4225761187 ≤ c.NB0) (budget : c.chooseCost ≤ Y.clock) :
    RunBounded Y mergeChoose c.chooseCost ∧
      ∀ post, evaluateHOLFiniteState Y mergeChoose = (none,post) →
        ∃ (b p' : BitVec 64) (R' : Set (BitVec 64)) (Z' : BitVec 64 → Nat × Nat),
          post.locals.lookup (ofString "binner") = some (.val (.word b)) ∧ b ∈ R' ∧
          c.CoreW (IB + 1) II post p' R' Z' ∧ ∀ k, k ≠ ofString "binner" → post.locals.lookup k = Y.locals.lookup k := by
  have guard := merge_guard_m Y f mv mL
  have h8 : 22 ≤ htabNewCost 8 := by decide
  have a1 := core.1
  have hp := core.2.2.2.2.1
  have newArgs : evalListHOLFinite Y (h := fun a => Classical.propDecidable (Y.memaddrs a)) [.const 32,.const 8] =
      some [.val (.word 32),.val (.word 8)] := by rw [evalListHOLFinite_eq_toExact]; rfl
  have newB : RunBounded Y (.call (some (some (.local,ofString "binner"),none)) (ofString "htab_new") [.const 32,.const 8])
      (htabNewCost 8 + 1) := by
    refine RunBounded.call newArgs (by unfold MergeCtx.chooseCost at budget; omega) ?_
    intro body locals rs lookup
    rw [htabNew_installed Y 32 8 a1] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨rfl,rfl,rfl⟩ := lookup
    exact evaluate_htabNew_body_bounded _ 32 8 p (by exact a1)
      (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) (by exact hp) core.2.2.2.2.2.2.1
      core.2.2.2.2.2.2.2.1 (by change _ ≤ Y.clock - 1; unfold MergeCtx.chooseCost at budget; omega)
  -- after the fresh table: the set call
  have afterNew : ∀ next, evaluateHOLFiniteState Y (.call (some (some (.local,ofString "binner"),none))
      (ofString "htab_new") [.const 32,.const 8]) = (none,next) →
      ∃ (p' : BitVec 64) (Z' : BitVec 64 → Nat × Nat),
        next.locals.lookup (ofString "binner") = some (.val (.word p)) ∧
        (∀ k, k ≠ ofString "binner" → next.locals.lookup k = Y.locals.lookup k) ∧
        c.CoreW IB II next p' (insert p R) Z' := by
    intro next run
    obtain ⟨p',Z',h1,h2,h3,_,_⟩ := MergeCtx.CoreW.after_new st Y next p R Z core
      (by unfold MergeCtx.chooseCost at budget; omega) run
    exact ⟨p',Z',h1,h2,h3⟩
  have setArgs : ∀ next : PanSemStateFiniteExact 64 F, next.locals.lookup (ofString "binner") = some (.val (.word p)) →
      (∀ k, k ≠ ofString "binner" → next.locals.lookup k = Y.locals.lookup k) →
      evalListHOLFinite next (h := fun a => Classical.propDecidable (next.memaddrs a))
        [.var .local (ofString "bouter"),.rfield 1 (.var .local (ofString "s")),.var .local (ofString "binner")] =
        some [.val (.word c.BO),.val (.word kp),.val (.word p)] := by
    intro next bn others
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,bn,others (ofString "bouter") (by decide),others (ofString "s") (by decide),boL,sL]
  constructor
  · unfold mergeChoose
    refine RunBounded.iteWord Y _ _ guard (fun _ => ?_) (fun _ => ?_)
    · unfold mergeNewSet MergeCtx.chooseCost
      refine RunBounded.seq newB (by unfold MergeCtx.chooseCost at budget; omega) ?_
      intro next run nextCode clk
      obtain ⟨p',Z',bn,others,⟨n1,n2,n3,n4,n5,n6,n7,n8,n9,⟨bc,bk,bu,bv,bo,bp,bn',bb,binv,bt,br,bvt,btop,bnb,bcb,bz⟩,_⟩⟩ :=
        afterNew next run
      have hdr : c.BO.toNat + 72 ≤ p'.toNat := by
        have := MergeCtx.Bouter.zone_below bc bk bu bv bo bp bn' bb binv btop c.BO.toNat (Or.inl ⟨le_refl _,by omega⟩)
        have := binv.headerKeys; have := binv.keysBefore; have := binv.usedBefore; have := binv.orderBefore; omega
      have bud : setBodyCost c.KB bc bn' + 1 ≤ c.setCost := by
        have := setBodyCost_mono c.KB bc (BitVec.ofNat 64 c.CB) bn' (BitVec.ofNat 64 c.CB)
          (by rw [ofNat_toNat_small _ (by have := st.cbSmall; omega)]; omega)
          (by rw [ofNat_toNat_small _ (by have := st.cbSmall; omega)]; omega)
          (by rw [ofNat_toNat_small _ (by have := st.cbSmall; omega)]; have := st.cbSmall; omega)
        unfold MergeCtx.setCost; omega
      exact RunBounded.weaken (runBounded_htabSet_call_laid next none _ _ _ c.KB c.BO bk c.SB bc bu bv bo bp bn' kp p p' bb
        (min bk.toNat bv.toNat) (bp.toNat + bc.toNat * 8) (Or.inl ⟨binv,rfl,rfl⟩) (setArgs next bn others) n5 n7 hdr n8
        (fun a h1 h2 h3 => by rw [n2]; exact st.arena a h1 (by have := st.LB; omega) h3) br st.kbSmall (by omega)) bud
    · exact RunBounded.weaken (RunBounded.ofProg (ProgBounded.straight _ (by decide)) a1 (Nat.zero_le _)) (Nat.zero_le _)
  · intro post run
    unfold mergeChoose at run
    rcases ite_normal_cases_cond Y post _ _ _ run with ⟨gw,gnz,gcond,yes⟩ | ⟨gcond,no⟩
    · rw [guard] at gcond
      simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at gcond
      unfold mergeNewSet at yes
      rw [evaluateHOLFiniteState_seq_line780] at yes
      cases newRun : evaluateHOLFiniteState Y (.call (some (some (.local,ofString "binner"),none)) (ofString "htab_new")
          [.const 32,.const 8]) with
      | mk nr next =>
        rw [newRun] at yes
        cases nr with
        | some r => simp at yes
        | none =>
          simp only at yes
          obtain ⟨p',Z',bn,others,core'⟩ := afterNew next newRun
          have newBound := newB
          unfold RunBounded at newBound
          rw [newRun] at newBound
          obtain ⟨nb1,_,_⟩ := newBound
          dsimp only at nb1
          have sb : c.setCost ≤ next.clock := by unfold MergeCtx.chooseCost at budget; omega
          obtain ⟨p'',core'',locals''⟩ := MergeCtx.CoreW.after_setK st next post p' (insert p R) Z' core' _ _ _ kp p
            (Set.mem_insert _ _) (setArgs next bn others) hCB hNB sb yes
          exact ⟨p,p'',insert p R,Z',by rw [locals'']; exact bn,Set.mem_insert _ _,core'',
            fun k ne => by rw [locals'']; exact others k ne⟩
    · rw [guard] at gcond
      simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at gcond
      have fne : f ≠ 0 := by intro h; simp [h] at gcond
      have mem : mv ∈ R := by rcases hit with h | h; exact absurd h fne; exact h
      have e := merge_assign_binner Y post f mv mL binL no
      subst e
      refine ⟨mv,p,R,Z,by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],mem,
        MergeCtx.CoreW.weaken (IB' := IB + 1) (II' := II) (core.transfer rfl rfl rfl rfl rfl) (Nat.le_succ _) (le_refl _),fun k ne => ?_⟩
      simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne]


set_option maxHeartbeats 2000000 in
theorem merge_union_boundedK {c : MergeCtx} (st : c.Static) (hNS : c.NS ≤ 4225761187)
    {IB II : Nat} {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p : BitVec 64) (R : Set (BitVec 64)) (Z : BitVec 64 → Nat × Nat)
    (core : c.CoreW IB II s p R Z) (dstArgument srcArgument : ExpHOL 64) (b v : BitVec 64) (member : b ∈ R)
    (src : c.SrcTab s v)
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [dstArgument,srcArgument] =
      some [.val (.word b),.val (.word v)])
    (budget : c.unionCostK ≤ s.clock) :
    RunBounded s (.call (some (none,none)) (ofString "htab_union_into") [dstArgument,srcArgument]) c.unionCostK := by
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,_,⟨ii,io,ip⟩⟩ := core
  have ofB := st.ofBelow
  obtain ⟨cap0,keys0,stride0,used0,vals0,order0,op0,count0,bits0,laid,tables,room,hTop,hL,hN,hC⟩ := ii b member
  obtain ⟨skl,skeys,sstride,scap,sused,svals,sorder,sorderPos,sn,sbits,sinv,stables,snB,foot⟩ := src
  have hdrLe := laid.header_le_hi
  have cap0K : cap0.toNat ≤ 4225761187 := by have := laid.regions.endBound; omega
  have bud := c.unionCostK_mono hNS b stride0 v sn skeys sstride svals sorder count0 cap0 p
    (Z b).1 (Z b).2 s cap0K (by omega) snB
  refine RunBounded.weaken (runBounded_union_tables s _ _ c.KI b keys0 stride0 cap0 used0 vals0 order0 op0 count0 bits0
    (Z b).1 (Z b).2 laid tables room v skl skeys sstride scap sused svals sorder sorderPos sn sbits sinv stables args p a5 a7
    a8 (by omega) (fun a h1 h2 h3 => by rw [a2]; exact st.arena a h1 (by omega) h3) (by rw [st.kI]; decide)
    (fun w h => by
      have hf := foot _ (Or.inr h)
      have := ofB _ hf
      have nz := io b member w.toNat
      unfold TZone at nz
      refine ⟨by omega,?_,?_⟩
      · by_cases x : b.toNat ≤ w.toNat
        · right; by_contra y; exact nz (Or.inl ⟨x,by omega⟩) hf
        · left; omega
      · by_cases x : (Z b).1 ≤ w.toNat
        · right; by_contra y; exact nz (Or.inr ⟨x,by omega⟩) hf
        · left; omega)
    (by omega)) bud


def MergeCtx.innerCostK (c : MergeCtx) : Nat := c.getCost + 1 + (c.chooseCost + c.unionCostK)


set_option maxHeartbeats 4000000 in
/-- One inner step: get on the block map, the choice of the inner table, and the nested union. -/
theorem merge_innerK {c : MergeCtx} (st : c.Static) (hNS : c.NS ≤ 4225761187) {I : Nat}
    {F : Type} (X : PanSemStateFiniteExact 64 F) (p : BitVec 64) (R : Set (BitVec 64))
    (Z : BitVec 64 → Nat × Nat) (core : c.CoreW I I X p R Z) (b0 kp v : BitVec 64)
    (sL : X.locals.lookup (ofString "s") = some (.rStruct [.val (.word b0),.val (.word kp),.val (.word v)]))
    (boL : X.locals.lookup (ofString "bouter") = some (.val (.word c.BO))) (src : c.SrcTab X v)
    (hCB : 4225761187 ≤ c.CB) (hNB : 4225761187 ≤ c.NB0) (hCI : 4225761187 ≤ c.CI) (hNI : 4225761187 ≤ c.NI0)
    (budget : c.innerCostK ≤ X.clock) :
    RunBounded X mergeInner c.innerCostK ∧
      ∀ post, evaluateHOLFiniteState X mergeInner = (none,post) →
        (∃ (p' : BitVec 64) (R' : Set (BitVec 64)) (Z' : BitVec 64 → Nat × Nat), c.CoreW (I + 1) (I + 1) post p' R' Z') ∧
        ∀ k, k ≠ ofString "m" → k ≠ ofString "binner" → post.locals.lookup k = X.locals.lookup k := by
  have a1 := core.1
  have args : evalListHOLFinite X (h := fun a => Classical.propDecidable (X.memaddrs a))
      [.var .local (ofString "bouter"),.rfield 1 (.var .local (ofString "s"))] =
      some [.val (.word c.BO),.val (.word kp)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,boL,sL]
  have lk := pan_two_word_lookup_shape X.code.lookup (ofString "htab_get") (ofString "t") (ofString "key")
    (sourceFunctionBody Guest.guestFn_htab_get) (.comb [.one,.one]) c.BO kp (by decide)
    (by rw [a1]; exact originalRuntimeCode_hashGet_lookup)
  -- the state after the get call, with the binner declaration
  have resumed : ∀ (value : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState (callEntryStateHOLFinite X
        ((HolFiniteMapExact.empty.update (ofString "t",.val (.word c.BO))).update (ofString "key",.val (.word kp))))
        (sourceFunctionBody Guest.guestFn_htab_get) = (some (.returned value),post) →
      ∃ f mv : BitVec 64, value = .rStruct [.val (.word f),.val (.word mv)] ∧ (f = 0 ∨ mv ∈ R) ∧
        post.memory = X.memory ∧ post.globals = X.globals ∧ post.memaddrs = X.memaddrs ∧ post.be = X.be ∧
        post.code = X.code := by
    intro value post run
    obtain ⟨f,mv,e,hit⟩ := merge_get_result X p R Z core kp value post run
    have frame := htabGet_memoryFrame (callEntryStateHOLFinite X
      ((HolFiniteMapExact.empty.update (ofString "t",.val (.word c.BO))).update (ofString "key",.val (.word kp)))) (by exact a1)
    have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite X
      ((HolFiniteMapExact.empty.update (ofString "t",.val (.word c.BO))).update (ofString "key",.val (.word kp))))
      (sourceFunctionBody Guest.guestFn_htab_get)
    rw [run] at frame meta'
    exact ⟨f,mv,e,hit,frame.1,frame.2,meta'.2.1,meta'.2.2.1,meta'.1⟩
  have getB : RunBounded (callEntryStateHOLFinite X
      ((HolFiniteMapExact.empty.update (ofString "t",.val (.word c.BO))).update (ofString "key",.val (.word kp))))
      (sourceFunctionBody Guest.guestFn_htab_get) c.getCost := by
    obtain ⟨_,_,_,_,_,_,_,_,_,⟨bc,bk,bu,bv,bo,bp,bn,bb,binv,bt,br,bvt,btop,bnb,bcb,bz⟩,_⟩ := core
    have m : bc.toNat * (4 * c.KB.toNat + 1 + 0 + 1) ≤ c.CB * (4 * c.KB.toNat + 1 + 0 + 1) := Nat.mul_le_mul_right _ bcb
    refine RunBounded.weaken (evaluate_htabGet_body_bounded _ c.KB c.BO bk c.SB bc bu bv bo bp bn kp bb
      (binv.transfer rfl rfl rfl rfl)
      (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) br st.kbSmall
      (by change _ ≤ X.clock - 1; unfold MergeCtx.innerCostK MergeCtx.getCost at budget; omega)) (by unfold MergeCtx.getCost; omega)
  -- the tail from the resumed state
  have tail : ∀ (T : PanSemStateFiniteExact 64 F) (f mv : BitVec 64),
      T.memory = X.memory → T.globals = X.globals → T.memaddrs = X.memaddrs → T.be = X.be → T.code = X.code →
      T.locals.lookup (ofString "m") = some (.rStruct [.val (.word f),.val (.word mv)]) →
      (∀ k, k ≠ ofString "m" → T.locals.lookup k = X.locals.lookup k) → (f = 0 ∨ mv ∈ R) →
      c.chooseCost + c.unionCostK ≤ T.clock →
      RunBounded T (.dec (ofString "binner") .one (.const 0) (.seq mergeChoose mergeUnionInner))
        (c.chooseCost + c.unionCostK) ∧
      ∀ post, evaluateHOLFiniteState T (.dec (ofString "binner") .one (.const 0) (.seq mergeChoose mergeUnionInner)) =
        (none,post) → (∃ p' R' Z', c.CoreW (I + 1) (I + 1) post p' R' Z') ∧
          ∀ k, k ≠ ofString "binner" → post.locals.lookup k = T.locals.lookup k := by
    intro T f mv tm tg ta tb tc tmL tO hit tb'
    have coreT := core.transfer tm ta tb tc tg
    generalize hU : setVarHOLFinite (ofString "binner") (.val (.word 0)) T = U
    have coreU : c.CoreW I I U p R Z := by rw [← hU]; exact coreT.transfer rfl rfl rfl rfl rfl
    have uL : ∀ k, k ≠ ofString "binner" → U.locals.lookup k = T.locals.lookup k := by
      intro k ne; rw [← hU]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne]
    have uBin : U.locals.lookup (ofString "binner") = some (.val (.word 0)) := by
      rw [← hU]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have uClock : U.clock = T.clock := by rw [← hU]; rfl
    have uM := (uL _ (by decide)).trans tmL
    have uS := (uL _ (by decide)).trans ((tO _ (by decide)).trans sL)
    have uB := (uL _ (by decide)).trans ((tO _ (by decide)).trans boL)
    have ch := merge_chooseK st U p R Z coreU f mv b0 kp v uM uS uB uBin hit hCB hNB (by omega)
    have srcU : c.SrcTab U v := src.between core coreU
    have unionB : ∀ next, evaluateHOLFiniteState U mergeChoose = (none,next) → c.unionCostK ≤ next.clock →
        RunBounded next mergeUnionInner c.unionCostK := by
      intro next run clk
      obtain ⟨b,p',R',Z',bn,mem,core',others⟩ := ch.2 next run
      have uargs : evalListHOLFinite next (h := fun a => Classical.propDecidable (next.memaddrs a))
          [.var .local (ofString "binner"),.rfield 2 (.var .local (ofString "s"))] =
          some [.val (.word b),.val (.word v)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact,evalHOLExact,bn,others (ofString "s") (by decide),uS]
      exact merge_union_boundedK st hNS next p' R' Z' core' _ _ b v mem (srcU.between coreU core') uargs clk
    constructor
    · rw [← hU] at *
      refine RunBounded.decConst T _ _ ?_
      rw [hU]
      exact RunBounded.seq ch.1 (by omega) (fun next run _ clk => unionB next run clk)
    · intro post run
      obtain ⟨bv',inner,be',innerRun,pm,pa,pb,pc,_,pg,plocals⟩ := dec_normal_globals run
      simp only [evalHOLExact] at be'
      cases be'
      rw [hU] at innerRun
      rw [evaluateHOLFiniteState_seq_line780] at innerRun
      cases chRun : evaluateHOLFiniteState U mergeChoose with
      | mk cr next =>
        rw [chRun] at innerRun
        cases cr with
        | some r => simp at innerRun
        | none =>
          simp only at innerRun
          obtain ⟨b,p',R',Z',bn,mem,core',others⟩ := ch.2 next chRun
          have chB := ch.1
          unfold RunBounded at chB
          rw [chRun] at chB
          obtain ⟨cb1,_,_⟩ := chB
          dsimp only at cb1
          have uargs : evalListHOLFinite next (h := fun a => Classical.propDecidable (next.memaddrs a))
              [.var .local (ofString "binner"),.rfield 2 (.var .local (ofString "s"))] =
              some [.val (.word b),.val (.word v)] := by
            rw [evalListHOLFinite_eq_toExact]
            simp [evalListHOLExact,evalHOLExact,bn,others (ofString "s") (by decide),uS]
          obtain ⟨skl,skeys,sstride,scap,sused,svals,sorder,sorderPos,sn,sbits,sinv,stables,snB,foot⟩ :=
            (srcU.between coreU core')
          obtain ⟨p'',Z'',core'',locals'',_,_⟩ := MergeCtx.CoreW.after_unionK st hNS next inner p' R' Z' core'
            _ _ b mem v skl skeys sstride scap sused svals sorder sorderPos sn sbits sinv stables snB
            (fun w h => foot w (Or.inr h)) uargs hCI hNI (by omega) innerRun
          refine ⟨⟨p'',R',Z'',core''.transfer pm pa pb pc pg⟩,fun k ne => ?_⟩
          rw [plocals k ne,locals'',others k ne,uL k ne]
  constructor
  · unfold mergeInner
    refine RunBounded.decCall args (by unfold MergeCtx.innerCostK at budget; omega) ?_
    intro body locals rs lookup
    rw [lk] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨rfl,rfl,rfl⟩ := lookup
    refine ⟨getB,fun value post run tc => ?_⟩
    obtain ⟨f,mv,e,hit,pm,pg,pa,pb,pc⟩ := resumed value post run
    subst e
    exact (tail (setVarHOLFinite (ofString "m") (ValueHOL.rStruct [ValueHOL.val (HolWordLab.word f),
      ValueHOL.val (HolWordLab.word mv)]) {post with locals := X.locals}) f mv pm pg pa pb pc
      (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      (fun k ne => by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne]) hit tc).1
  · intro post run
    unfold mergeInner at run
    obtain ⟨vals,body,callee,rs,w,bodyPost,res,inner,args',lookup',bodyRun,rm,ra,rb,rc,rg,rclk,rname,rothers,contRun,
      pm,pa,pb,pc,pg,plocals⟩ := decCall_normal_globals run
    rw [args] at args'
    simp only [Option.some.injEq] at args'
    subst args'
    rw [lk] at lookup'
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup'
    obtain ⟨rfl,rfl,rfl⟩ := lookup'
    obtain ⟨f,mv,e,hit,bm,bg,ba,bbe,bc⟩ := resumed w bodyPost bodyRun
    subst e
    have gb := getB
    unfold RunBounded at gb
    rw [bodyRun] at gb
    obtain ⟨g1,g2,_⟩ := gb
    dsimp only at g1 g2
    change X.clock - 1 ≤ bodyPost.clock + c.getCost at g1
    have resClock := rclk g2
    obtain ⟨⟨p'',R',Z'',core''⟩,locs⟩ := (tail res f mv (rm.trans bm) (rg.trans bg) (ra.trans ba) (rb.trans bbe)
      (rc.trans bc) rname rothers hit (by rw [resClock]; unfold MergeCtx.innerCostK at budget; omega)).2 inner contRun
    refine ⟨⟨p'',R',Z'',core''.transfer pm pa pb pc pg⟩,fun k nm nb => ?_⟩
    rw [plocals k nm,locs k nb,rothers k nm]


/-- Layout clamps: every table capacity is at most limit/8, so these bounds always hold for the constants limit/8. -/
structure MergeCtx.BoundsK (c : MergeCtx) : Prop where
  hCB : 4225761187 ≤ c.CB
  hNB : 4225761187 ≤ c.NB0
  hCI : 4225761187 ≤ c.CI
  hNI : 4225761187 ≤ c.NI0
  hNS : c.NS ≤ 4225761187
  nSmall : c.n.toNat < 2 ^ 62

def MergeCtx.iterCostK (c : MergeCtx) : Nat := 1 + 1 + (c.innerCostK + 0)


set_option maxHeartbeats 4000000 in
/-- One storage-loop iteration from a ranked state with a remaining outer item. -/
theorem merge_iterK {c : MergeCtx} (st : c.Static) (bd : c.BoundsK) {F : Type} (d : PanSemStateFiniteExact 64 F)
    (outer : c.OuterOK d) (I : BitVec 64) (lt : I.toNat < c.n.toNat)
    (iL : d.locals.lookup (ofString "i") = some (.val (.word I)))
    (capL : d.locals.lookup (ofString "cap") = some (.val (.word c.n)))
    (oL : d.locals.lookup (ofString "outer") = some (.val (.word c.O)))
    (boL : d.locals.lookup (ofString "bouter") = some (.val (.word c.BO)))
    (p : BitVec 64) (R : Set (BitVec 64)) (Z : BitVec 64 → Nat × Nat) (core : c.CoreW I.toNat I.toNat d p R Z)
    (budget : c.iterCostK ≤ d.clock) :
    RunBounded d mergeIter c.iterCostK ∧
      ∀ post, evaluateHOLFiniteState d mergeIter = (none,post) →
        post.locals.lookup (ofString "i") = some (.val (.word (I + 1))) ∧
        post.locals.lookup (ofString "cap") = some (.val (.word c.n)) ∧
        post.locals.lookup (ofString "outer") = some (.val (.word c.O)) ∧
        post.locals.lookup (ofString "bouter") = some (.val (.word c.BO)) ∧
        ∃ p' R' Z', c.CoreW (I.toNat + 1) (I.toNat + 1) post p' R' Z' := by
  have a1 := core.1
  have args : evalListHOLFinite d (h := fun a => Classical.propDecidable (d.memaddrs a))
      [.var .local (ofString "outer"),.var .local (ofString "i")] = some [.val (.word c.O),.val (.word I)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,oL,iL]
  have lk := pan_two_word_lookup_shape d.code.lookup (ofString "htab_item") (ofString "t") (ofString "ordinal")
    (sourceFunctionBody Guest.guestFn_htab_item) (.comb [.one,.one,.one]) c.O I (by decide)
    (by rw [a1]; exact vmLookup_htab_item)
  have itemPB : ProgBounded (sourceFunctionBody Guest.guestFn_htab_item) 1 := by
    obtain ⟨ps,bd',rs',lk',pb⟩ := vmBound_htab_item
    rw [vmLookup_htab_item] at lk'
    simp only [Option.some.injEq,Prod.mk.injEq] at lk'
    obtain ⟨_,rfl,_⟩ := lk'
    exact pb
  -- the resumed state after the item read
  have resumed : ∀ (value : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState (callEntryStateHOLFinite d
        ((HolFiniteMapExact.empty.update (ofString "t",ValueHOL.val (HolWordLab.word c.O))).update
          (ofString "ordinal",ValueHOL.val (HolWordLab.word I))))
        (sourceFunctionBody Guest.guestFn_htab_item) = (some (.returned value),post) →
      ∃ b0 kp v : BitVec 64, value = .rStruct [.val (.word b0),.val (.word kp),.val (.word v)] ∧ c.SrcTab d v ∧
        post.memory = d.memory ∧ post.globals = d.globals ∧ post.memaddrs = d.memaddrs ∧ post.be = d.be ∧
        post.code = d.code := by
    intro value post run
    obtain ⟨b0,kp,v,e,src⟩ := merge_item d outer p R Z core I lt value post run
    have frame := htabItem_memoryFrame (callEntryStateHOLFinite d
      ((HolFiniteMapExact.empty.update (ofString "t",ValueHOL.val (HolWordLab.word c.O))).update
        (ofString "ordinal",ValueHOL.val (HolWordLab.word I)))) (by exact a1)
    have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite d
      ((HolFiniteMapExact.empty.update (ofString "t",ValueHOL.val (HolWordLab.word c.O))).update
        (ofString "ordinal",ValueHOL.val (HolWordLab.word I)))) (sourceFunctionBody Guest.guestFn_htab_item)
    rw [run] at frame meta'
    exact ⟨b0,kp,v,e,src,frame.1,frame.2,meta'.2.1,meta'.2.2.1,meta'.1⟩
  -- the iteration tail from a resumed state
  have tail : ∀ (T : PanSemStateFiniteExact 64 F) (b0 kp v : BitVec 64),
      T.memory = d.memory → T.globals = d.globals → T.memaddrs = d.memaddrs → T.be = d.be → T.code = d.code →
      T.locals.lookup (ofString "s") = some (.rStruct [.val (.word b0),.val (.word kp),.val (.word v)]) →
      (∀ k, k ≠ ofString "s" → T.locals.lookup k = d.locals.lookup k) → c.SrcTab d v → c.innerCostK ≤ T.clock →
      RunBounded T (.seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s"))) (.const 0)) mergeInner .skip)
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1]))) (c.innerCostK + 0) ∧
      ∀ post, evaluateHOLFiniteState T (.seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s"))) (.const 0))
          mergeInner .skip) (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1]))) = (none,post) →
        post.locals.lookup (ofString "i") = some (.val (.word (I + 1))) ∧
        (∀ k, k ≠ ofString "i" → k ≠ ofString "m" → k ≠ ofString "binner" → post.locals.lookup k = T.locals.lookup k) ∧
        ∃ p' R' Z', c.CoreW (I.toNat + 1) (I.toNat + 1) post p' R' Z' := by
    intro T b0 kp v tm tg ta tb tc tS tO src tk
    have coreT := core.transfer tm ta tb tc tg
    have srcT : c.SrcTab T v := src.between core coreT
    have boT := (tO _ (by decide)).trans boL
    have iT := (tO _ (by decide)).trans iL
    have inner := merge_innerK st bd.hNS T p R Z coreT b0 kp v tS boT srcT bd.hCB bd.hNB bd.hCI bd.hNI tk
    obtain ⟨gw,guard⟩ := union_guard_word T b0 kp v tS
    constructor
    · refine RunBounded.seq (RunBounded.iteWord T _ gw guard (fun _ => inner.1) (fun _ =>
        RunBounded.weaken (RunBounded.ofProg (ProgBounded.straight _ (by decide)) (tc.trans a1) (Nat.zero_le _))
          (Nat.zero_le _))) (by omega) ?_
      intro next _ nc _
      exact RunBounded.ofProg (ProgBounded.straight _ (by decide)) (nc.trans (tc.trans a1)) (Nat.zero_le _)
    · intro post run
      rw [evaluateHOLFiniteState_seq_line780] at run
      cases iteRun : evaluateHOLFiniteState T (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s")))
          (.const 0)) mergeInner .skip) with
      | mk ir mid =>
        rw [iteRun] at run
        cases ir with
        | some r => simp at run
        | none =>
          simp only at run
          have key : (∀ k, k ≠ ofString "m" → k ≠ ofString "binner" → mid.locals.lookup k = T.locals.lookup k) ∧
              ∃ p' R' Z', c.CoreW (I.toNat + 1) (I.toNat + 1) mid p' R' Z' := by
            rcases ite_normal_cases_cond T mid _ _ _ iteRun with ⟨_,_,_,yes⟩ | ⟨_,no⟩
            · exact ⟨(inner.2 mid yes).2,(inner.2 mid yes).1⟩
            · rw [evaluateHOLFiniteState_skip] at no
              obtain ⟨_,rfl⟩ := Prod.mk.inj no
              exact ⟨fun _ _ _ => rfl,p,R,Z,MergeCtx.CoreW.weaken (IB' := I.toNat + 1) (II' := I.toNat + 1) coreT
                (Nat.le_succ _) (Nat.le_succ _)⟩
          obtain ⟨mlocals,p',R',Z',core'⟩ := key
          have mI : mid.locals.lookup (ofString "i") = some (.val (.word I)) := by
            rw [mlocals _ (by decide) (by decide)]; exact iT
          rw [evaluate_increment_local mid (ofString "i") I mI] at run
          obtain ⟨_,rfl⟩ := Prod.mk.inj run
          refine ⟨by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],fun k ni nm nb => ?_,
            p',R',Z',core'.transfer rfl rfl rfl rfl rfl⟩
          simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ni]
          exact mlocals k nm nb
  constructor
  · unfold mergeIter
    refine RunBounded.decCall args (by unfold MergeCtx.iterCostK at budget; omega) ?_
    intro body locals rs lookup
    rw [lk] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨rfl,rfl,rfl⟩ := lookup
    refine ⟨RunBounded.ofProg itemPB (by exact a1) (by change 1 ≤ d.clock - 1; unfold MergeCtx.iterCostK at budget; omega),
      fun value post run tc => ?_⟩
    obtain ⟨b0,kp,v,e,src,pm,pg,pa,pb,pc⟩ := resumed value post run
    subst e
    exact (tail (setVarHOLFinite (ofString "s") (ValueHOL.rStruct [ValueHOL.val (HolWordLab.word b0),
      ValueHOL.val (HolWordLab.word kp),ValueHOL.val (HolWordLab.word v)]) {post with locals := d.locals}) b0 kp v
      pm pg pa pb pc (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      (fun k ne => by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne]) src
      (by change _ ≤ post.clock; omega)).1
  · intro post run
    unfold mergeIter at run
    obtain ⟨vals,body,callee,rs,w,bodyPost,res,inner,args',lookup',bodyRun,rm,ra,rb,rc,rg,rclk,rname,rothers,contRun,
      pm,pa,pb,pc,pg,plocals⟩ := decCall_normal_globals run
    rw [args] at args'
    simp only [Option.some.injEq] at args'
    subst args'
    rw [lk] at lookup'
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup'
    obtain ⟨rfl,rfl,rfl⟩ := lookup'
    obtain ⟨b0,kp,v,e,src,bm,bg,ba,bbe,bc⟩ := resumed w bodyPost bodyRun
    subst e
    have ib := itemPB (callEntryStateHOLFinite d
      ((HolFiniteMapExact.empty.update (ofString "t",ValueHOL.val (HolWordLab.word c.O))).update
        (ofString "ordinal",ValueHOL.val (HolWordLab.word I)))) (by exact a1)
      (by change 1 ≤ d.clock - 1; unfold MergeCtx.iterCostK at budget; omega)
    rw [bodyRun] at ib
    obtain ⟨i1,i2,_⟩ := ib
    change d.clock - 1 ≤ bodyPost.clock + 1 at i1
    have resClock := rclk i2
    obtain ⟨tI,tL,p',R',Z',core'⟩ := (tail res b0 kp v (rm.trans bm) (rg.trans bg) (ra.trans ba) (rb.trans bbe)
      (rc.trans bc) rname rothers src (by rw [resClock]; unfold MergeCtx.iterCostK at budget; omega)).2 inner contRun
    have keep : ∀ k, k ≠ ofString "s" → k ≠ ofString "i" → k ≠ ofString "m" → k ≠ ofString "binner" →
        post.locals.lookup k = d.locals.lookup k := fun k ns ni nm nb => by
      rw [plocals k ns,tL k ni nm nb,rothers k ns]
    exact ⟨by rw [plocals _ (by decide)]; exact tI,by rw [keep _ (by decide) (by decide) (by decide) (by decide)]; exact capL,
      by rw [keep _ (by decide) (by decide) (by decide) (by decide)]; exact oL,
      by rw [keep _ (by decide) (by decide) (by decide) (by decide)]; exact boL,
      p',R',Z',core'.transfer pm pa pb pc pg⟩


/-- The storage loop from rank m runs within m * (iterCost + 1) ticks; a normal exit keeps the rank. -/
theorem mergeLoop_runK {c : MergeCtx} (st : c.Static) (bd : c.BoundsK) :
    ∀ m : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
      MergeRankO c state m → m * (c.iterCostK + 1) ≤ state.clock →
      RankedOutcome state mergeCond (m * (c.iterCostK + 1)) (MergeRankO c) False
        (evaluateHOLFiniteState state (.while mergeCond mergeIter)) := by
  have nSmall : c.n.toNat < 2 ^ 63 := by have := bd.nSmall; omega
  refine rankedWhile_run mergeCond mergeIter c.iterCostK (MergeRankO c) False ?_ ?_
  · intro G s ranked v hv
    obtain ⟨⟨I,iL,ILe,left,capL,_⟩,_⟩ := ranked
    unfold mergeCond at hv
    rw [eval_localBound_less s (ofString "i") (ofString "cap") .less (Or.inl rfl) I c.n (by omega) nSmall iL capL] at hv
    have : ¬ I.toNat < c.n.toNat := by omega
    simp [this] at hv
    exact hv.symm
  · intro G s k v code' ranked hv nonzero budget'
    have rankedD : MergeRankO c (decClockHOLFinite s) (k + 1) := ranked.transfer rfl rfl rfl rfl rfl rfl
    obtain ⟨⟨I,iL,ILe,left,capL,oL,bL,p,R,Z,core⟩,outer⟩ := rankedD
    unfold mergeCond at hv
    rw [eval_localBound_less s (ofString "i") (ofString "cap") .less (Or.inl rfl) I c.n (by omega) nSmall iL capL] at hv
    have lt : I.toNat < c.n.toNat := by
      by_cases h : I.toNat < c.n.toNat
      · exact h
      · simp [h] at hv; exact absurd hv.symm nonzero
    have it := merge_iterK st bd (decClockHOLFinite s) outer I lt iL capL oL bL p R Z core
      (by change _ ≤ s.clock - 1; omega)
    obtain ⟨b1,b2,b3⟩ := it.1
    have noWrap : (I + 1).toNat = I.toNat + 1 := by
      rw [BitVec.toNat_add_of_lt (by change I.toNat + 1 < 2 ^ 64; omega)]; rfl
    refine ⟨b1,b2,b3,?_,?_⟩
    · intro flow
      rcases flow with normal | cont
      · cases hrun : evaluateHOLFiniteState (decClockHOLFinite s) mergeIter with
        | mk r post =>
          rw [hrun] at normal
          simp only at normal
          subst normal
          obtain ⟨pI,pCap,pO,pB,p',R',Z',core'⟩ := it.2 post hrun
          refine ⟨k,le_refl _,⟨⟨I + 1,pI,by rw [noWrap]; omega,by rw [noWrap]; omega,pCap,pO,pB,p',R',Z',
            by rw [noWrap]; exact core'⟩,outer.between core core'⟩,core'.1.trans code'.symm⟩
      · exact absurd cont (evaluate_noTopContinue mergeIter (by decide) (decClockHOLFinite s))
    · intro brk
      exact absurd brk (evaluate_noTopBreak mergeIter (by decide) (decClockHOLFinite s))


set_option maxHeartbeats 4000000 in
/-- The `merge_tx_into_block` storage loop: from the loop invariant at count bound 0 and the outer-map facts,
a returned run returns 0 with the invariant at count bound n (block map with registry values, registered
inner tables apart, outer footprint unchanged, heap monotone). -/
theorem mergeTail_returnedK {c : MergeCtx} (st : c.Static) (bd : c.BoundsK) {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) (T B : BitVec 64)
    (hT : state.globals.lookup (ofString "ts") = some (.val (.word T)))
    (hB : state.globals.lookup (ofString "bs") = some (.val (.word B)))
    (dO : state.memaddrs (T + 32)) (cO : state.memory (T + 32) = .word c.O)
    (dBO : state.memaddrs (B + 32)) (cBO : state.memory (B + 32) = .word c.BO)
    (dn : state.memaddrs (c.O + 24)) (cn : state.memory (c.O + 24) = .word c.n)
    (p : BitVec 64) (R : Set (BitVec 64)) (Z : BitVec 64 → Nat × Nat) (core : c.CoreW 0 0 state p R Z)
    (outer : c.OuterOK state) (budget : c.n.toNat * (c.iterCostK + 1) ≤ state.clock)
    (run : evaluateHOLFiniteState state mergeTailE = (some (.returned v),post)) :
    v = .val (.word 0) ∧ ∃ p' R' Z', c.CoreW c.n.toNat c.n.toNat post p' R' Z' := by
  obtain ⟨e1,e2,e3⟩ := mergeTail_entry state T B hT hB dO cO dBO cBO dn cn
  unfold mergeTailE at run
  obtain ⟨v1,i1,ev1,r1,m1,a1,b1,c1,g1⟩ := dec_returned_globals run
  rw [e1] at ev1; cases ev1
  obtain ⟨v2,i2,ev2,r2,m2,a2,b2,c2,g2⟩ := dec_returned_globals r1
  rw [e2] at ev2; cases ev2
  obtain ⟨v3,i3,ev3,r3,m3,a3,b3,c3,g3⟩ := dec_returned_globals r2
  rw [e3] at ev3; cases ev3
  obtain ⟨v4,i4,ev4,r4,m4,a4,b4,c4,g4⟩ := dec_returned_globals r3
  rw [item_eval_const] at ev4; cases ev4
  have rank0 := mergeTail_rank0 state p R Z core outer
  generalize hs4 : setVarHOLFinite (ofString "i") (.val (.word 0)) (setVarHOLFinite (ofString "cap") (.val (.word c.n))
    (setVarHOLFinite (ofString "bouter") (.val (.word c.BO)) (setVarHOLFinite (ofString "outer") (.val (.word c.O)) state)))
    = s4 at r4 rank0
  have s4code : s4.code = originalRuntimeCode := by rw [← hs4]; exact core.1
  have s4clock : s4.clock = state.clock := by rw [← hs4]; rfl
  rw [evaluateHOLFiniteState_seq_line780] at r4
  cases loopRun : evaluateHOLFiniteState s4 (.while mergeCond mergeIter) with
  | mk lr ls =>
    rw [loopRun] at r4
    cases lr with
    | some r =>
      exfalso
      obtain ⟨e,_⟩ := Prod.mk.inj r4
      simp only [Option.some.injEq] at e
      subst e
      exact mergeLoop_not_returned s4 ls v loopRun
    | none =>
      simp only at r4
      have outcome := mergeLoop_runK st bd c.n.toNat s4 s4code rank0 (by rw [s4clock]; exact budget)
      rw [loopRun] at outcome
      obtain ⟨_,_,_,normal⟩ := outcome
      obtain ⟨m,⟨⟨I,iL,ILe,_,capL,_,_,p',R',Z',core'⟩,_⟩,_,exit⟩ := normal rfl
      have nSmall : c.n.toNat < 2 ^ 63 := by have := bd.nSmall; omega
      have IN : I.toNat = c.n.toNat := by
        rcases exit with zero | f
        · unfold mergeCond at zero
          rw [eval_localBound_less ls (ofString "i") (ofString "cap") .less (Or.inl rfl) I c.n (by omega) nSmall iL capL]
            at zero
          by_cases lt : I.toNat < c.n.toNat
          · simp [lt] at zero
          · omega
        · exact f.elim
      obtain ⟨ve,rm,ra,rb,rc,rg⟩ := return_const_globals ls i4 0 v r4
      refine ⟨ve,p',R',Z',?_⟩
      rw [IN] at core'
      exact core'.transfer (m1.trans (m2.trans (m3.trans (m4.trans rm)))) (a1.trans (a2.trans (a3.trans (a4.trans ra))))
        (b1.trans (b2.trans (b3.trans (b4.trans rb)))) (c1.trans (c2.trans (c3.trans (c4.trans rc))))
        (g1.trans (g2.trans (g3.trans (g4.trans rg))))


set_option maxHeartbeats 2000000 in
/-- The storage loop costs at most n * (iterCost + 1) ticks in every outcome. -/
theorem runBounded_mergeTailK {c : MergeCtx} (st : c.Static) (bd : c.BoundsK) {F : Type}
    (state : PanSemStateFiniteExact 64 F) (T B : BitVec 64)
    (hT : state.globals.lookup (ofString "ts") = some (.val (.word T)))
    (hB : state.globals.lookup (ofString "bs") = some (.val (.word B)))
    (dO : state.memaddrs (T + 32)) (cO : state.memory (T + 32) = .word c.O)
    (dBO : state.memaddrs (B + 32)) (cBO : state.memory (B + 32) = .word c.BO)
    (dn : state.memaddrs (c.O + 24)) (cn : state.memory (c.O + 24) = .word c.n)
    (p : BitVec 64) (R : Set (BitVec 64)) (Z : BitVec 64 → Nat × Nat) (core : c.CoreW 0 0 state p R Z)
    (outer : c.OuterOK state) (budget : c.n.toNat * (c.iterCostK + 1) ≤ state.clock) :
    RunBounded state mergeTailE (c.n.toNat * (c.iterCostK + 1) + 0) := by
  obtain ⟨e1,e2,e3⟩ := mergeTail_entry state T B hT hB dO cO dBO cBO dn cn
  have rank0 := mergeTail_rank0 state p R Z core outer
  unfold mergeTailE
  refine RunBounded.decWord state _ _ c.O e1 ?_
  refine RunBounded.decWord _ _ _ c.BO e2 ?_
  refine RunBounded.decWord _ _ _ c.n e3 ?_
  refine RunBounded.decConst _ _ _ ?_
  have whole : RunBounded (setVarHOLFinite (ofString "i") (.val (.word 0)) (setVarHOLFinite (ofString "cap")
      (.val (.word c.n)) (setVarHOLFinite (ofString "bouter") (.val (.word c.BO))
        (setVarHOLFinite (ofString "outer") (.val (.word c.O)) state))))
      (.seq (.while mergeCond mergeIter) (.return (.const 0))) (c.n.toNat * (c.iterCostK + 1) + 0) := by
    refine RunBounded.seq ?_ (by change _ ≤ state.clock; omega) ?_
    · obtain ⟨o1,o2,o3,_⟩ := mergeLoop_runK st bd c.n.toNat (setVarHOLFinite (ofString "i") (.val (.word 0))
        (setVarHOLFinite (ofString "cap") (.val (.word c.n)) (setVarHOLFinite (ofString "bouter") (.val (.word c.BO))
          (setVarHOLFinite (ofString "outer") (.val (.word c.O)) state)))) (by exact core.1) rank0
        (by change _ ≤ state.clock; exact budget)
      exact ⟨o1,o2,o3⟩
    · intro next _ nextCode _
      exact RunBounded.ofProg (ProgBounded.straight _ (by decide)) (nextCode.trans core.1) (Nat.zero_le _)
  exact whole


#print axioms merge_chooseK
#print axioms merge_union_boundedK
#print axioms merge_innerK
#print axioms merge_iterK
#print axioms mergeLoop_runK
#print axioms mergeTail_returnedK
#print axioms runBounded_mergeTailK
end InitECandidate.Runtime
