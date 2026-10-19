import InitECandidate.Runtime.HtabMergeCore
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-! The `merge_tx_into_block` storage loop composed: one iteration (`merge_iter`: item read, `htab_get` on
the block map, fresh `htab_new` + `htab_set` or the found inner table, nested `htab_union_into`, counter),
the ranked loop (`mergeLoop_run`), and the loop contract `mergeTail_returned` with its all-outcome bound
`runBounded_mergeTail`. -/

/-- An outer-side source table in state s whose reads and footprint lie in the outer footprint. -/
def MergeCtx.SrcTab (c : MergeCtx) {F : Type} (s : PanSemStateFiniteExact 64 F) (v : BitVec 64) : Prop :=
  ∃ (skl skeys sstride scap sused svals sorder sorderPos sn : BitVec 64) (sbits : Nat),
    HtabRegions skl v skeys sstride scap sused svals sorder sorderPos sn sbits s ∧
    OrderInv s scap sn sused sorder sorderPos ∧ sn.toNat ≤ c.NS ∧
    ∀ w, (HtabFoot v scap sused sorder sorderPos w ∨ (v.toNat ≤ w ∧ w < v.toNat + 72) ∨
      (sorder.toNat ≤ w ∧ w < sorder.toNat + scap.toNat * 8) ∨ (svals.toNat ≤ w ∧ w < svals.toNat + scap.toNat * 8)) →
      c.OFoot w

theorem MergeCtx.SrcTab.move {c : MergeCtx} {F G : Type} {s : PanSemStateFiniteExact 64 F}
    {r : PanSemStateFiniteExact 64 G} {v : BitVec 64} (t : c.SrcTab s v)
    (memaddrs : r.memaddrs = s.memaddrs) (be : r.be = s.be) (code : r.code = s.code)
    (keep : ∀ w : BitVec 64, c.OFoot w.toNat → r.memory w = s.memory w) : c.SrcTab r v := by
  obtain ⟨skl,skeys,sstride,scap,sused,svals,sorder,sorderPos,sn,sbits,sinv,stables,snB,foot⟩ := t
  have K := sinv.foot_keep (r := r) (fun w h => keep w (foot _ (Or.inl h)))
  exact ⟨skl,skeys,sstride,scap,sused,svals,sorder,sorderPos,sn,sbits,
    sinv.congr memaddrs be code (fun w h => keep w (foot _ (Or.inl h))),
    stables.congr sinv.count_le memaddrs be K.2.1 K.2.2.1 K.2.2.2,snB,foot⟩

/-- Through the loop invariant, a source table valid at entry is valid in every state. -/
theorem MergeCtx.SrcTab.atCore {c : MergeCtx} {F : Type} {s0 s : PanSemStateFiniteExact 64 F} {v : BitVec 64}
    (t : c.SrcTab s0 v) (m0 : c.M0 = s0.memory) (a0 : c.A0 = s0.memaddrs) (be0 : c.BE = s0.be)
    (code0 : s0.code = originalRuntimeCode) {IB II : Nat} {p : BitVec 64} {R : Set (BitVec 64)}
    {Z : BitVec 64 → Nat × Nat} (core : c.CoreW IB II s p R Z) : c.SrcTab s v :=
  t.move (core.2.1.trans a0) (core.2.2.1.trans be0) (core.1.trans code0.symm)
    (fun w h => by rw [core.2.2.2.1 w h,m0])

#print axioms MergeCtx.SrcTab.atCore

def MergeCtx.chooseCost (c : MergeCtx) : Nat := (htabNewCost 8 + 1) + c.setCost

theorem merge_guard_m {F : Type} (Y : PanSemStateFiniteExact 64 F) (f mv : BitVec 64)
    (mL : Y.locals.lookup (ofString "m") = some (.rStruct [.val (.word f),.val (.word mv)])) :
    @evalHOLExact 64 F _ Y.toExact (fun a => Classical.propDecidable (Y.memaddrs a))
      (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0)) =
      some (.val (.word (if f = 0 then 1 else 0))) := by
  simp [evalHOLExact,mL,Compiler.Encoders.Asm.wordCmpHOL]

theorem merge_assign_binner {F : Type} (Y post : PanSemStateFiniteExact 64 F) (f mv : BitVec 64)
    (mL : Y.locals.lookup (ofString "m") = some (.rStruct [.val (.word f),.val (.word mv)]))
    (binL : Y.locals.lookup (ofString "binner") = some (.val (.word 0)))
    (run : evaluateHOLFiniteState Y (.assign .local (ofString "binner") (.rfield 1 (.var .local (ofString "m")))) =
      (none,post)) : post = setVarHOLFinite (ofString "binner") (.val (.word mv)) Y := by
  simp [evaluateHOLFiniteState_assign,evalHOLExact,mL,binL,lookupKvarHOLExact,isValidValueHOLExact,setKvarHOLFinite,
    shapeOfHOLExact,shapeEqHOL] at run
  exact run.symm

set_option maxHeartbeats 4000000 in
/-- The choice of the inner table: a fresh registered table stored into the block map on a miss, the found
registered table on a hit. -/
theorem merge_choose {c : MergeCtx} (st : c.Static) {IB II : Nat} {F : Type} (Y : PanSemStateFiniteExact 64 F)
    (p : BitVec 64) (R : Set (BitVec 64)) (Z : BitVec 64 → Nat × Nat) (core : c.CoreW IB II Y p R Z)
    (f mv b0 kp v : BitVec 64)
    (mL : Y.locals.lookup (ofString "m") = some (.rStruct [.val (.word f),.val (.word mv)]))
    (sL : Y.locals.lookup (ofString "s") = some (.rStruct [.val (.word b0),.val (.word kp),.val (.word v)]))
    (boL : Y.locals.lookup (ofString "bouter") = some (.val (.word c.BO)))
    (binL : Y.locals.lookup (ofString "binner") = some (.val (.word 0)))
    (hit : f = 0 ∨ mv ∈ R) (cbBound : 4 * (c.NB0 + IB + 1) ≤ c.CB) (budget : c.chooseCost ≤ Y.clock) :
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
          obtain ⟨p'',core'',locals''⟩ := MergeCtx.CoreW.after_set st next post p' (insert p R) Z' core' _ _ _ kp p
            (Set.mem_insert _ _) (setArgs next bn others) cbBound sb yes
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

#print axioms merge_choose

/-- The union call's all-outcome bound from table invariants. -/
theorem runBounded_union_tables {F : Type} (state : PanSemStateFiniteExact 64 F) (dstArgument srcArgument : ExpHOL 64)
    (keyLength dst keys stride capacity used values order orderPos count : BitVec 64) (bits lo hi : Nat)
    (laid : HtabLaid keyLength dst keys stride capacity used values order orderPos count bits lo hi state)
    (tables : OrderInv state capacity count used order orderPos) (room : count.toNat < capacity.toNat)
    (src sKeyLength skeys sstride scapacity sused svalues sorder sorderPos n : BitVec 64) (sbits : Nat)
    (sinv : HtabRegions sKeyLength src skeys sstride scapacity sused svalues sorder sorderPos n sbits state)
    (stables : OrderInv state scapacity n sused sorder sorderPos)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [dstArgument,srcArgument] =
      some [.val (.word dst),.val (.word src)])
    (pointer : BitVec 64) (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerAligned : pointer.toNat % 8 = 0) (pointerInside : pointer.toNat ≤ 33806089496)
    (headerBelow : dst.toNat + 72 ≤ pointer.toNat)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → dst.toNat ≤ a.toNat → a.toNat < 33806089496 → state.memaddrs a)
    (small : keyLength.toNat ≤ 33806089496)
    (srcAway : ∀ w : BitVec 64, ((src.toNat ≤ w.toNat ∧ w.toNat < src.toNat + 72) ∨
      (sorder.toNat ≤ w.toNat ∧ w.toNat < sorder.toNat + scapacity.toNat * 8) ∨
      (svalues.toNat ≤ w.toNat ∧ w.toNat < svalues.toNat + scapacity.toNat * 8)) →
        w.toNat < pointer.toNat ∧ (w.toNat < dst.toNat ∨ dst.toNat + 72 ≤ w.toNat) ∧ (w.toNat < lo ∨ hi ≤ w.toNat))
    (budget : n.toNat * ((unionCtxOf keyLength dst stride src n skeys sstride svalues sorder count capacity pointer
      lo hi state).stepCost + 1) + 1 ≤ state.clock) :
    RunBounded state (.call (some (none,none)) (ofString "htab_union_into") [dstArgument,srcArgument])
      (n.toNat * ((unionCtxOf keyLength dst stride src n skeys sstride svalues sorder count capacity pointer
        lo hi state).stepCost + 1) + 1) := by
  have dReg := laid.regions
  have dEnd := dReg.endBound
  have sOrd := sinv.orderEnd
  have sLe := sinv.count_le
  have ok : (unionCtxOf keyLength dst stride src n skeys sstride svalues sorder count capacity pointer lo hi state).Ok :=
    ⟨headerBelow,pointerAligned,pointerInside,arena,small,by change capacity.toNat ≤ _; omega,
      by change n.toNat ≤ _; omega,room⟩
  have reads := UnionCtx.srcReads_of_table
    (unionCtxOf keyLength dst stride src n skeys sstride svalues sorder count capacity pointer lo hi state) state rfl rfl
    sKeyLength scapacity sused sorderPos sbits sinv stables (fun w h => srcAway w h)
  have te := sinv.tableEnd
  exact runBounded_htabUnionInto_callT _ ok reads state none dstArgument srcArgument laid.code args
    (sinv.header_domain 24 (by omega) (by omega)) sinv.cell24 rfl rfl rfl
    ⟨keys,used,values,order,orderPos,bits,laid,tables⟩ heap budget

#print axioms runBounded_union_tables

set_option maxHeartbeats 2000000 in
theorem merge_union_bounded {c : MergeCtx} (st : c.Static) (uSmall : 4 * (c.NIM + c.NS) ≤ 33806089496)
    {IB II : Nat} (hII : II ≤ c.n.toNat) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p : BitVec 64) (R : Set (BitVec 64)) (Z : BitVec 64 → Nat × Nat)
    (core : c.CoreW IB II s p R Z) (dstArgument srcArgument : ExpHOL 64) (b v : BitVec 64) (member : b ∈ R)
    (src : c.SrcTab s v)
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [dstArgument,srcArgument] =
      some [.val (.word b),.val (.word v)])
    (budget : c.unionCost ≤ s.clock) :
    RunBounded s (.call (some (none,none)) (ofString "htab_union_into") [dstArgument,srcArgument]) c.unionCost := by
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,_,⟨ii,io,ip⟩⟩ := core
  have ofB := st.ofBelow
  obtain ⟨cap0,keys0,stride0,used0,vals0,order0,op0,count0,bits0,laid,tables,room,hTop,hL,hN,hC⟩ := ii b member
  obtain ⟨skl,skeys,sstride,scap,sused,svals,sorder,sorderPos,sn,sbits,sinv,stables,snB,foot⟩ := src
  have hdrLe := laid.header_le_hi
  have mulLe : II * c.NS ≤ c.n.toNat * c.NS := Nat.mul_le_mul_right _ hII
  have bud := c.unionCost_mono uSmall st.ciSmall b stride0 v sn skeys sstride svals sorder count0 cap0 p
    (Z b).1 (Z b).2 s hC (by unfold MergeCtx.NIM; omega) snB
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

#print axioms merge_union_bounded

theorem MergeCtx.SrcTab.between {c : MergeCtx} {F : Type} {s r : PanSemStateFiniteExact 64 F} {v : BitVec 64}
    (t : c.SrcTab s v) {IB II IB' II' : Nat} {p p' : BitVec 64} {R R' : Set (BitVec 64)}
    {Z Z' : BitVec 64 → Nat × Nat} (cs : c.CoreW IB II s p R Z) (cr : c.CoreW IB' II' r p' R' Z') : c.SrcTab r v :=
  t.move (cr.2.1.trans cs.2.1.symm) (cr.2.2.1.trans cs.2.2.1.symm) (cr.1.trans cs.1.symm)
    (fun w h => by rw [cr.2.2.2.1 w h,cs.2.2.2.1 w h])

theorem dec_normal_globals {F : Type} {s post : PanSemStateFiniteExact 64 F} {name : MlS} {shape : ShapeHOL}
    {initializer : ExpHOL 64} {body : ProgHOL 64}
    (run : evaluateHOLFiniteState s (.dec name shape initializer body) = (none,post)) :
    ∃ value inner, @evalHOLExact 64 F _ s.toExact (fun address => Classical.propDecidable (s.memaddrs address))
        initializer = some value ∧
      evaluateHOLFiniteState (setVarHOLFinite name value s) body = (none,inner) ∧
      post.memory = inner.memory ∧ post.memaddrs = inner.memaddrs ∧ post.be = inner.be ∧ post.code = inner.code ∧
      post.clock = inner.clock ∧ post.globals = inner.globals ∧
      (∀ k, k ≠ name → post.locals.lookup k = inner.locals.lookup k) := by
  rw [evaluateHOLFiniteState_dec_total] at run
  dsimp only at run
  split at run
  · simp at run
  · rename_i value evaluated
    split at run
    · cases inner : evaluateHOLFiniteState (setVarHOLFinite name value s) body with
      | mk r i =>
        rw [inner] at run
        obtain ⟨e,p⟩ := Prod.mk.inj run
        simp only at e
        subst p
        refine ⟨value,i,evaluated,by rw [inner,e],rfl,rfl,rfl,rfl,rfl,rfl,fun k ne => ?_⟩
        rw [resVarEq_lookup,if_neg ne]
    · simp at run

def MergeCtx.getCost (c : MergeCtx) : Nat :=
  c.KB.toNat / 8 + 8 + 1 + (c.CB * (4 * c.KB.toNat + 1 + 0 + 1) + 0) + 1 + 0

def MergeCtx.innerCost (c : MergeCtx) : Nat := c.getCost + 1 + (c.chooseCost + c.unionCost)

/-- The facts of the get call's resumed state: the result is a miss, or a hit on a registered table. -/
theorem merge_get_result {c : MergeCtx} {IB II : Nat} {F : Type} (X : PanSemStateFiniteExact 64 F) (p : BitVec 64)
    (R : Set (BitVec 64)) (Z : BitVec 64 → Nat × Nat) (core : c.CoreW IB II X p R Z) (kp : BitVec 64)
    (value : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite X
      ((HolFiniteMapExact.empty.update (ofString "t",.val (.word c.BO))).update (ofString "key",.val (.word kp))))
      (sourceFunctionBody Guest.guestFn_htab_get) = (some (.returned value),post)) :
    ∃ f mv : BitVec 64, value = .rStruct [.val (.word f),.val (.word mv)] ∧ (f = 0 ∨ mv ∈ R) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,⟨bc,bk,bu,bv,bo,bp,bn,bb,binv,bt,br,bvt,_⟩,_⟩ := core
  rcases htabGet_returned_value (callEntryStateHOLFinite X
      ((HolFiniteMapExact.empty.update (ofString "t",ValueHOL.val (HolWordLab.word c.BO))).update
        (ofString "key",ValueHOL.val (HolWordLab.word kp))))
      post value c.KB c.BO bk c.SB bc bu bv bo bp bn kp bb
      (by exact binv.toRegions.transfer rfl rfl rfl rfl)
      (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) run with e | ⟨q,val,lt,occ,cell,e⟩
  · exact ⟨0,0,e,Or.inl rfl⟩
  · exact ⟨1,val,e,Or.inr (bvt.2.1 q lt occ val cell)⟩

set_option maxHeartbeats 4000000 in
/-- One inner step: get on the block map, the choice of the inner table, and the nested union. -/
theorem merge_inner {c : MergeCtx} (st : c.Static) (uSmall : 4 * (c.NIM + c.NS) ≤ 33806089496) {I : Nat}
    (hI : I < c.n.toNat) {F : Type} (X : PanSemStateFiniteExact 64 F) (p : BitVec 64) (R : Set (BitVec 64))
    (Z : BitVec 64 → Nat × Nat) (core : c.CoreW I I X p R Z) (b0 kp v : BitVec 64)
    (sL : X.locals.lookup (ofString "s") = some (.rStruct [.val (.word b0),.val (.word kp),.val (.word v)]))
    (boL : X.locals.lookup (ofString "bouter") = some (.val (.word c.BO))) (src : c.SrcTab X v)
    (cbBound : 4 * (c.NB0 + I + 1) ≤ c.CB) (ciBound : 4 * (c.NI0 + (I + 1) * c.NS) ≤ c.CI)
    (budget : c.innerCost ≤ X.clock) :
    RunBounded X mergeInner c.innerCost ∧
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
      (by change _ ≤ X.clock - 1; unfold MergeCtx.innerCost MergeCtx.getCost at budget; omega)) (by unfold MergeCtx.getCost; omega)
  -- the tail from the resumed state
  have tail : ∀ (T : PanSemStateFiniteExact 64 F) (f mv : BitVec 64),
      T.memory = X.memory → T.globals = X.globals → T.memaddrs = X.memaddrs → T.be = X.be → T.code = X.code →
      T.locals.lookup (ofString "m") = some (.rStruct [.val (.word f),.val (.word mv)]) →
      (∀ k, k ≠ ofString "m" → T.locals.lookup k = X.locals.lookup k) → (f = 0 ∨ mv ∈ R) →
      c.chooseCost + c.unionCost ≤ T.clock →
      RunBounded T (.dec (ofString "binner") .one (.const 0) (.seq mergeChoose mergeUnionInner))
        (c.chooseCost + c.unionCost) ∧
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
    have ch := merge_choose st U p R Z coreU f mv b0 kp v uM uS uB uBin hit cbBound (by omega)
    have srcU : c.SrcTab U v := src.between core coreU
    have unionB : ∀ next, evaluateHOLFiniteState U mergeChoose = (none,next) → c.unionCost ≤ next.clock →
        RunBounded next mergeUnionInner c.unionCost := by
      intro next run clk
      obtain ⟨b,p',R',Z',bn,mem,core',others⟩ := ch.2 next run
      have uargs : evalListHOLFinite next (h := fun a => Classical.propDecidable (next.memaddrs a))
          [.var .local (ofString "binner"),.rfield 2 (.var .local (ofString "s"))] =
          some [.val (.word b),.val (.word v)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact,evalHOLExact,bn,others (ofString "s") (by decide),uS]
      exact merge_union_bounded st uSmall (by omega) next p' R' Z' core' _ _ b v mem (srcU.between coreU core') uargs clk
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
          obtain ⟨p'',Z'',core'',locals'',_,_⟩ := MergeCtx.CoreW.after_union st uSmall (by omega) next inner p' R' Z' core'
            _ _ b mem v skl skeys sstride scap sused svals sorder sorderPos sn sbits sinv stables snB
            (fun w h => foot w (Or.inr h)) uargs ciBound (by omega) innerRun
          refine ⟨⟨p'',R',Z'',core''.transfer pm pa pb pc pg⟩,fun k ne => ?_⟩
          rw [plocals k ne,locals'',others k ne,uL k ne]
  constructor
  · unfold mergeInner
    refine RunBounded.decCall args (by unfold MergeCtx.innerCost at budget; omega) ?_
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
      (rc.trans bc) rname rothers hit (by rw [resClock]; unfold MergeCtx.innerCost at budget; omega)).2 inner contRun
    refine ⟨⟨p'',R',Z'',core''.transfer pm pa pb pc pg⟩,fun k nm nb => ?_⟩
    rw [plocals k nm,locs k nb,rothers k nm]

#print axioms merge_inner

/-- The outer map at entry: the item reads (header words, order entries, value words) are mapped words in
the outer footprint, and every value is a valid source table. -/
def MergeCtx.OuterOK (c : MergeCtx) {F : Type} (s0 : PanSemStateFiniteExact 64 F) : Prop :=
  (s0.memaddrs (c.O + 56) ∧ s0.memory (c.O + 56) = .word c.oorder ∧ c.OFoot (c.O + 56).toNat) ∧
  (s0.memaddrs (c.O + 32) ∧ s0.memory (c.O + 32) = .word c.okeys ∧ c.OFoot (c.O + 32).toNat) ∧
  (s0.memaddrs (c.O + 8) ∧ s0.memory (c.O + 8) = .word c.ostride ∧ c.OFoot (c.O + 8).toNat) ∧
  (s0.memaddrs (c.O + 40) ∧ s0.memory (c.O + 40) = .word c.ovals ∧ c.OFoot (c.O + 40).toNat) ∧
  ∀ k : BitVec 64, k.toNat < c.n.toNat → ∃ slot v : BitVec 64,
    s0.memaddrs (c.oorder + k * 8) ∧ s0.memory (c.oorder + k * 8) = .word slot ∧ c.OFoot (c.oorder + k * 8).toNat ∧
    s0.memaddrs (c.ovals + slot * 8) ∧ s0.memory (c.ovals + slot * 8) = .word v ∧ c.OFoot (c.ovals + slot * 8).toNat ∧
    c.SrcTab s0 v

/-- Count bounds that keep every iteration inside the uniform costs. -/
structure MergeCtx.Bounds (c : MergeCtx) : Prop where
  cb : 4 * (c.NB0 + c.n.toNat) ≤ c.CB
  ci : 4 * (c.NI0 + c.n.toNat * c.NS) ≤ c.CI
  uSmall : 4 * (c.NIM + c.NS) ≤ 33806089496
  nSmall : c.n.toNat < 2 ^ 62

def MergeCtx.iterCost (c : MergeCtx) : Nat := 1 + 1 + (c.innerCost + 0)

/-- The item read of iteration I, through the loop invariant. -/
theorem merge_item {c : MergeCtx} {F : Type} {IB II : Nat} (s : PanSemStateFiniteExact 64 F) (outer : c.OuterOK s) (p : BitVec 64) (R : Set (BitVec 64)) (Z : BitVec 64 → Nat × Nat)
    (core : c.CoreW IB II s p R Z) (I : BitVec 64) (lt : I.toNat < c.n.toNat) (value : ValueHOL 64)
    (post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite s
      ((HolFiniteMapExact.empty.update (ofString "t",ValueHOL.val (HolWordLab.word c.O))).update
        (ofString "ordinal",ValueHOL.val (HolWordLab.word I))))
      (sourceFunctionBody Guest.guestFn_htab_item) = (some (.returned value),post)) :
    ∃ b0 kp v : BitVec 64, value = .rStruct [.val (.word b0),.val (.word kp),.val (.word v)] ∧ c.SrcTab s v := by
  obtain ⟨⟨d56,m56,o56⟩,⟨d32,m32,o32⟩,⟨d8,m8,o8⟩,⟨d40,m40,o40⟩,items⟩ := outer
  obtain ⟨slot,v,dO,mO,oO,dV,mV,oV,srcV⟩ := items I lt
  obtain ⟨b,e⟩ := htabItem_returned (callEntryStateHOLFinite s
      ((HolFiniteMapExact.empty.update (ofString "t",ValueHOL.val (HolWordLab.word c.O))).update
        (ofString "ordinal",ValueHOL.val (HolWordLab.word I))))
    post value c.O I c.oorder slot c.okeys c.ostride c.ovals v (by exact core.1)
    (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by change s.memaddrs _; exact d56) (by change s.memory _ = _; exact m56)
    (by change s.memaddrs _; exact dO) (by change s.memory _ = _; exact mO)
    (by change s.memaddrs _; exact d32) (by change s.memory _ = _; exact m32)
    (by change s.memaddrs _; exact d8) (by change s.memory _ = _; exact m8)
    (by change s.memaddrs _; exact d40) (by change s.memory _ = _; exact m40)
    (by change s.memaddrs _; exact dV) (by change s.memory _ = _; exact mV) run
  exact ⟨b,_,v,e,srcV⟩

#print axioms merge_item

set_option maxHeartbeats 4000000 in
/-- One storage-loop iteration from a ranked state with a remaining outer item. -/
theorem merge_iter {c : MergeCtx} (st : c.Static) (bd : c.Bounds) {F : Type} (d : PanSemStateFiniteExact 64 F)
    (outer : c.OuterOK d) (I : BitVec 64) (lt : I.toNat < c.n.toNat)
    (iL : d.locals.lookup (ofString "i") = some (.val (.word I)))
    (capL : d.locals.lookup (ofString "cap") = some (.val (.word c.n)))
    (oL : d.locals.lookup (ofString "outer") = some (.val (.word c.O)))
    (boL : d.locals.lookup (ofString "bouter") = some (.val (.word c.BO)))
    (p : BitVec 64) (R : Set (BitVec 64)) (Z : BitVec 64 → Nat × Nat) (core : c.CoreW I.toNat I.toNat d p R Z)
    (budget : c.iterCost ≤ d.clock) :
    RunBounded d mergeIter c.iterCost ∧
      ∀ post, evaluateHOLFiniteState d mergeIter = (none,post) →
        post.locals.lookup (ofString "i") = some (.val (.word (I + 1))) ∧
        post.locals.lookup (ofString "cap") = some (.val (.word c.n)) ∧
        post.locals.lookup (ofString "outer") = some (.val (.word c.O)) ∧
        post.locals.lookup (ofString "bouter") = some (.val (.word c.BO)) ∧
        ∃ p' R' Z', c.CoreW (I.toNat + 1) (I.toNat + 1) post p' R' Z' := by
  have a1 := core.1
  have cbB : 4 * (c.NB0 + I.toNat + 1) ≤ c.CB := by have := bd.cb; omega
  have ciB : 4 * (c.NI0 + (I.toNat + 1) * c.NS) ≤ c.CI := by
    have := bd.ci
    have : (I.toNat + 1) * c.NS ≤ c.n.toNat * c.NS := Nat.mul_le_mul_right _ lt
    omega
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
      (∀ k, k ≠ ofString "s" → T.locals.lookup k = d.locals.lookup k) → c.SrcTab d v → c.innerCost ≤ T.clock →
      RunBounded T (.seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s"))) (.const 0)) mergeInner .skip)
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1]))) (c.innerCost + 0) ∧
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
    have inner := merge_inner st bd.uSmall lt T p R Z coreT b0 kp v tS boT srcT cbB ciB tk
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
    refine RunBounded.decCall args (by unfold MergeCtx.iterCost at budget; omega) ?_
    intro body locals rs lookup
    rw [lk] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨rfl,rfl,rfl⟩ := lookup
    refine ⟨RunBounded.ofProg itemPB (by exact a1) (by change 1 ≤ d.clock - 1; unfold MergeCtx.iterCost at budget; omega),
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
      (by change 1 ≤ d.clock - 1; unfold MergeCtx.iterCost at budget; omega)
    rw [bodyRun] at ib
    obtain ⟨i1,i2,_⟩ := ib
    change d.clock - 1 ≤ bodyPost.clock + 1 at i1
    have resClock := rclk i2
    obtain ⟨tI,tL,p',R',Z',core'⟩ := (tail res b0 kp v (rm.trans bm) (rg.trans bg) (ra.trans ba) (rb.trans bbe)
      (rc.trans bc) rname rothers src (by rw [resClock]; unfold MergeCtx.iterCost at budget; omega)).2 inner contRun
    have keep : ∀ k, k ≠ ofString "s" → k ≠ ofString "i" → k ≠ ofString "m" → k ≠ ofString "binner" →
        post.locals.lookup k = d.locals.lookup k := fun k ns ni nm nb => by
      rw [plocals k ns,tL k ni nm nb,rothers k ns]
    exact ⟨by rw [plocals _ (by decide)]; exact tI,by rw [keep _ (by decide) (by decide) (by decide) (by decide)]; exact capL,
      by rw [keep _ (by decide) (by decide) (by decide) (by decide)]; exact oL,
      by rw [keep _ (by decide) (by decide) (by decide) (by decide)]; exact boL,
      p',R',Z',core'.transfer pm pa pb pc pg⟩

#print axioms merge_iter

theorem MergeCtx.OuterOK.between {c : MergeCtx} {F : Type} {s r : PanSemStateFiniteExact 64 F}
    (o : c.OuterOK s) {IB II IB' II' : Nat} {p p' : BitVec 64} {R R' : Set (BitVec 64)}
    {Z Z' : BitVec 64 → Nat × Nat} (cs : c.CoreW IB II s p R Z) (cr : c.CoreW IB' II' r p' R' Z') : c.OuterOK r := by
  have ad : r.memaddrs = s.memaddrs := cr.2.1.trans cs.2.1.symm
  have mm : ∀ w : BitVec 64, c.OFoot w.toNat → r.memory w = s.memory w := fun w h => by
    rw [cr.2.2.2.1 w h,cs.2.2.2.1 w h]
  obtain ⟨⟨d56,m56,o56⟩,⟨d32,m32,o32⟩,⟨d8,m8,o8⟩,⟨d40,m40,o40⟩,items⟩ := o
  refine ⟨⟨by rw [ad]; exact d56,by rw [mm _ o56]; exact m56,o56⟩,⟨by rw [ad]; exact d32,by rw [mm _ o32]; exact m32,o32⟩,
    ⟨by rw [ad]; exact d8,by rw [mm _ o8]; exact m8,o8⟩,⟨by rw [ad]; exact d40,by rw [mm _ o40]; exact m40,o40⟩,
    fun k lt => ?_⟩
  obtain ⟨slot,v,dO,mO,oO,dV,mV,oV,src⟩ := items k lt
  exact ⟨slot,v,by rw [ad]; exact dO,by rw [mm _ oO]; exact mO,oO,by rw [ad]; exact dV,by rw [mm _ oV]; exact mV,oV,
    src.between cs cr⟩

/-- The storage-loop rank with the outer-map facts. -/
def MergeRankO (c : MergeCtx) {F : Type} (s : PanSemStateFiniteExact 64 F) (m : Nat) : Prop :=
  MergeRank c s m ∧ c.OuterOK s

theorem MergeRankO.transfer {c : MergeCtx} {F : Type} {s r : PanSemStateFiniteExact 64 F} {m : Nat}
    (ranked : MergeRankO c s m) (memory : r.memory = s.memory) (memaddrs : r.memaddrs = s.memaddrs) (be : r.be = s.be)
    (code : r.code = s.code) (globals : r.globals = s.globals) (locals : r.locals = s.locals) : MergeRankO c r m := by
  obtain ⟨⟨I,iL,a1,a2,capL,oL,bL,p,R,Z,core⟩,outer⟩ := ranked
  have core' := core.transfer memory memaddrs be code globals
  exact ⟨⟨I,by rw [locals]; exact iL,a1,a2,by rw [locals]; exact capL,by rw [locals]; exact oL,by rw [locals]; exact bL,
    p,R,Z,core'⟩,outer.between core core'⟩

/-- The storage loop from rank m runs within m * (iterCost + 1) ticks; a normal exit keeps the rank. -/
theorem mergeLoop_run {c : MergeCtx} (st : c.Static) (bd : c.Bounds) :
    ∀ m : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
      MergeRankO c state m → m * (c.iterCost + 1) ≤ state.clock →
      RankedOutcome state mergeCond (m * (c.iterCost + 1)) (MergeRankO c) False
        (evaluateHOLFiniteState state (.while mergeCond mergeIter)) := by
  have nSmall : c.n.toNat < 2 ^ 63 := by have := bd.nSmall; omega
  refine rankedWhile_run mergeCond mergeIter c.iterCost (MergeRankO c) False ?_ ?_
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
    have it := merge_iter st bd (decClockHOLFinite s) outer I lt iL capL oL bL p R Z core
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

#print axioms mergeLoop_run
def noTopReturnA : ProgHOL 64 → Bool
  | .seq first second => noTopReturnA first && noTopReturnA second
  | .ite _ yes no => noTopReturnA yes && noTopReturnA no
  | .dec _ _ _ body => noTopReturnA body
  | .decCall _ _ _ _ continuation => noTopReturnA continuation
  | .skip | .assign _ _ _ | .primitive _ _ _ | .store _ _ | .storeByte _ _ | .raise _ _ | .break | .continue
  | .extCall _ _ _ _ _ | .annot _ _ => true
  | .call (some (none,none)) _ _ => true
  | .call (some (some _,none)) _ _ => true
  | _ => false

theorem evaluate_noTopReturnA {F : Type} (program : ProgHOL 64) (supported : noTopReturnA program = true)
    (state : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) :
    (evaluateHOLFiniteState state program).1 ≠ some (.returned v) := by
  cases shape : program with
  | seq first second =>
    have children : noTopReturnA first = true ∧ noTopReturnA second = true := by
      simpa only [shape,noTopReturnA,Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_seq_line780]
    have one := evaluate_noTopReturnA first children.1 state v
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at one
      cases result with
      | none => exact evaluate_noTopReturnA second children.2 middle v
      | some r => exact one
  | ite condition yes no =>
    have children : noTopReturnA yes = true ∧ noTopReturnA no = true := by
      simpa only [shape,noTopReturnA,Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noTopReturnA no children.2 state v
      · exact evaluate_noTopReturnA yes children.1 state v
    · simp
  | dec name kind initializer body =>
    have child : noTopReturnA body = true := by simpa only [shape,noTopReturnA] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · rename_i value _
      split
      · cases inner : evaluateHOLFiniteState (setVarHOLFinite name value state) body with
        | mk r i =>
          have := evaluate_noTopReturnA body child (setVarHOLFinite name value state) v
          rw [inner] at this
          simpa [inner] using this
      · simp
  | decCall name shape' function arguments continuation =>
    have child : noTopReturnA continuation = true := by simpa only [shape,noTopReturnA] using supported
    intro hret
    cases run : evaluateHOLFiniteState state (.decCall name shape' function arguments continuation) with
    | mk result post =>
      rw [run] at hret
      dsimp only at hret
      subst hret
      obtain ⟨_,_,_,_,_,_,resumed,inner,_,_,_,_,_,_,_,_,_,_,contRun,_⟩ := decCall_returned_body run
      have := evaluate_noTopReturnA continuation child resumed v
      rw [contRun] at this
      exact this rfl
  | skip => simp [evaluateHOLFiniteState_skip]
  | «break» => simp [evaluateHOLFiniteState_break]
  | «continue» => simp [evaluateHOLFiniteState_continue]
  | annot tag text => simp [evaluateHOLFiniteState_annot]
  | raise name value =>
    rw [evaluateHOLFiniteState_raise]; split
    · dsimp only; split <;> simp
    · simp
  | store destination value => rcases (evaluate_store_control_frame state destination value).1 with h | h <;> rw [h] <;> simp
  | storeByte destination value => rcases (evaluate_storeByte_control_frame state destination value).1 with h | h <;> rw [h] <;> simp
  | assign kind name value =>
    rw [evaluateHOLFiniteState_assign]; split
    · simp
    · split <;> simp
  | primitive name operator arguments =>
    rw [evaluateHOLFiniteState_primitive]
    repeat' first | split | simp
  | extCall function a b c d =>
    rw [evaluateHOLFiniteState_extCall_source]
    repeat' first | split | simp
  | call info function arguments =>
    have handlerFree : info = some (none,none) ∨ ∃ d, info = some (some d,none) := by
      rcases info with _ | ⟨_ | d,_ | h⟩
      all_goals first | exact Or.inl rfl | exact Or.inr ⟨_,rfl⟩ | simp [shape,noTopReturnA] at supported
    rcases handlerFree with rfl | ⟨d,rfl⟩
    · exact fun h => discard_call_not_returned state function arguments v h
    · rw [evaluateHOLFiniteState_call]
      repeat' first | split | (simp; done) | simp_all
  | «return» value => simp [shape,noTopReturnA] at supported
  | «while» condition body => simp [shape,noTopReturnA] at supported
  | store32 _ _ => simp [shape,noTopReturnA] at supported
  | shMemLoad _ _ _ => simp [shape,noTopReturnA] at supported
  | shMemStore _ _ _ => simp [shape,noTopReturnA] at supported
  | tick => simp [shape,noTopReturnA] at supported

#print axioms evaluate_noTopReturnA

theorem mergeLoop_not_returned {F : Type} (s post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (run : evaluateHOLFiniteState s (.while mergeCond mergeIter) = (some (.returned v),post)) : False :=
  while_returned_invariant _ mergeIter (fun _ => True) (fun _ => False) (fun _ _ => trivial)
    (fun t w q _ r => evaluate_noTopReturnA mergeIter (by decide) t w (by rw [r])) (fun _ _ _ _ => trivial)
    s.clock s rfl trivial v post run

#print axioms mergeLoop_not_returned

/-- The entry of the storage loop: the record loads and the counter, giving rank n. -/
theorem mergeTail_entry {c : MergeCtx} {F : Type} (state : PanSemStateFiniteExact 64 F) (T B : BitVec 64)
    (hT : state.globals.lookup (ofString "ts") = some (.val (.word T)))
    (hB : state.globals.lookup (ofString "bs") = some (.val (.word B)))
    (dO : state.memaddrs (T + 32)) (cO : state.memory (T + 32) = .word c.O)
    (dBO : state.memaddrs (B + 32)) (cBO : state.memory (B + 32) = .word c.BO)
    (dn : state.memaddrs (c.O + 24)) (cn : state.memory (c.O + 24) = .word c.n) :
    @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
        (.load .one (.op .add [.var .global (ofString "ts"),.const 32])) = some (.val (.word c.O)) ∧
      @evalHOLExact 64 F _ (setVarHOLFinite (ofString "outer") (.val (.word c.O)) state).toExact
        (fun a => Classical.propDecidable ((setVarHOLFinite (ofString "outer") (.val (.word c.O)) state).memaddrs a))
        (.load .one (.op .add [.var .global (ofString "bs"),.const 32])) = some (.val (.word c.BO)) ∧
      @evalHOLExact 64 F _ (setVarHOLFinite (ofString "bouter") (.val (.word c.BO))
          (setVarHOLFinite (ofString "outer") (.val (.word c.O)) state)).toExact
        (fun a => Classical.propDecidable ((setVarHOLFinite (ofString "bouter") (.val (.word c.BO))
          (setVarHOLFinite (ofString "outer") (.val (.word c.O)) state)).memaddrs a))
        (.load .one (.op .add [.var .local (ofString "outer"),.const 24])) = some (.val (.word c.n)) := by
  refine ⟨eval_record_word state .global _ T 32 c.O (eval_global_word state _ T hT) dO cO,
    eval_record_word _ .global _ B 32 c.BO (eval_global_word _ _ B hB) dBO cBO,
    eval_record_word _ .local _ c.O 24 c.n (item_eval_locals _ _ c.O (by
      simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])) dn cn⟩

/-- The rank at the loop entry. -/
theorem mergeTail_rank0 {c : MergeCtx} {F : Type} (state : PanSemStateFiniteExact 64 F) (p : BitVec 64)
    (R : Set (BitVec 64)) (Z : BitVec 64 → Nat × Nat) (core : c.CoreW 0 0 state p R Z) (outer : c.OuterOK state) :
    MergeRankO c (setVarHOLFinite (ofString "i") (.val (.word 0)) (setVarHOLFinite (ofString "cap") (.val (.word c.n))
      (setVarHOLFinite (ofString "bouter") (.val (.word c.BO))
        (setVarHOLFinite (ofString "outer") (.val (.word c.O)) state)))) c.n.toNat :=
  ⟨⟨0,by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],by simp,by simp,
    by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],
    by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],
    by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],
    p,R,Z,core.transfer rfl rfl rfl rfl rfl⟩,
    outer.between core (core.transfer (r := setVarHOLFinite (ofString "i") (.val (.word 0))
      (setVarHOLFinite (ofString "cap") (.val (.word c.n)) (setVarHOLFinite (ofString "bouter") (.val (.word c.BO))
        (setVarHOLFinite (ofString "outer") (.val (.word c.O)) state)))) rfl rfl rfl rfl rfl)⟩

set_option maxHeartbeats 4000000 in
/-- The `merge_tx_into_block` storage loop: from the loop invariant at count bound 0 and the outer-map facts,
a returned run returns 0 with the invariant at count bound n (block map with registry values, registered
inner tables apart, outer footprint unchanged, heap monotone). -/
theorem mergeTail_returned {c : MergeCtx} (st : c.Static) (bd : c.Bounds) {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) (T B : BitVec 64)
    (hT : state.globals.lookup (ofString "ts") = some (.val (.word T)))
    (hB : state.globals.lookup (ofString "bs") = some (.val (.word B)))
    (dO : state.memaddrs (T + 32)) (cO : state.memory (T + 32) = .word c.O)
    (dBO : state.memaddrs (B + 32)) (cBO : state.memory (B + 32) = .word c.BO)
    (dn : state.memaddrs (c.O + 24)) (cn : state.memory (c.O + 24) = .word c.n)
    (p : BitVec 64) (R : Set (BitVec 64)) (Z : BitVec 64 → Nat × Nat) (core : c.CoreW 0 0 state p R Z)
    (outer : c.OuterOK state) (budget : c.n.toNat * (c.iterCost + 1) ≤ state.clock)
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
      have outcome := mergeLoop_run st bd c.n.toNat s4 s4code rank0 (by rw [s4clock]; exact budget)
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

#print axioms mergeTail_returned

set_option maxHeartbeats 2000000 in
/-- The storage loop costs at most n * (iterCost + 1) ticks in every outcome. -/
theorem runBounded_mergeTail {c : MergeCtx} (st : c.Static) (bd : c.Bounds) {F : Type}
    (state : PanSemStateFiniteExact 64 F) (T B : BitVec 64)
    (hT : state.globals.lookup (ofString "ts") = some (.val (.word T)))
    (hB : state.globals.lookup (ofString "bs") = some (.val (.word B)))
    (dO : state.memaddrs (T + 32)) (cO : state.memory (T + 32) = .word c.O)
    (dBO : state.memaddrs (B + 32)) (cBO : state.memory (B + 32) = .word c.BO)
    (dn : state.memaddrs (c.O + 24)) (cn : state.memory (c.O + 24) = .word c.n)
    (p : BitVec 64) (R : Set (BitVec 64)) (Z : BitVec 64 → Nat × Nat) (core : c.CoreW 0 0 state p R Z)
    (outer : c.OuterOK state) (budget : c.n.toNat * (c.iterCost + 1) ≤ state.clock) :
    RunBounded state mergeTailE (c.n.toNat * (c.iterCost + 1) + 0) := by
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
      (.seq (.while mergeCond mergeIter) (.return (.const 0))) (c.n.toNat * (c.iterCost + 1) + 0) := by
    refine RunBounded.seq ?_ (by change _ ≤ state.clock; omega) ?_
    · obtain ⟨o1,o2,o3,_⟩ := mergeLoop_run st bd c.n.toNat (setVarHOLFinite (ofString "i") (.val (.word 0))
        (setVarHOLFinite (ofString "cap") (.val (.word c.n)) (setVarHOLFinite (ofString "bouter") (.val (.word c.BO))
          (setVarHOLFinite (ofString "outer") (.val (.word c.O)) state)))) (by exact core.1) rank0
        (by change _ ≤ state.clock; exact budget)
      exact ⟨o1,o2,o3⟩
    · intro next _ nextCode _
      exact RunBounded.ofProg (ProgBounded.straight _ (by decide)) (nextCode.trans core.1) (Nat.zero_le _)
  exact whole

#print axioms runBounded_mergeTail
end InitECandidate.Runtime
