import InitECandidate.Runtime.HtabMergeClamp
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 2000000 in
/-- Carry the loop invariant across a step into a new context whose entry data is the new state: the step
keeps memory on the block-map zone and the registered zones, and the new outer footprint avoids them. -/
theorem MergeCtx.CoreW.move {c c' : MergeCtx} {IB II : Nat} {F : Type} {s r : PanSemStateFiniteExact 64 F}
    {p : BitVec 64} {R : Set (BitVec 64)} {Z : BitVec 64 → Nat × Nat} (core : c.CoreW IB II s p R Z)
    (memaddrs : r.memaddrs = s.memaddrs) (be : r.be = s.be) (code : r.code = s.code)
    (rel : HeapRel s.globals r.globals) (p' : BitVec 64)
    (hp' : r.globals.lookup (ofString "heap_ptr") = some (.val (.word p')))
    (eBO : c'.BO = c.BO) (eKB : c'.KB = c.KB) (eSB : c'.SB = c.SB) (eKI : c'.KI = c.KI) (eL : c'.L = c.L)
    (eNB : c'.NB0 = c.NB0) (eCB : c'.CB = c.CB) (eNI : c'.NI0 = c.NI0) (eCI : c'.CI = c.CI) (eNS : c'.NS = c.NS)
    (hM : c'.M0 = r.memory) (hA : c'.A0 = r.memaddrs) (hBE : c'.BE = r.be) (hG : c'.G0 = r.globals)
    (hP : c'.P0.toNat ≤ p'.toNat)
    (keepR : ∀ b ∈ R, ∀ w : BitVec 64, TZone b (Z b).1 (Z b).2 w.toNat → r.memory w = s.memory w)
    (keepB : ∀ bcap bkeys bused bvals border bop bcount : BitVec 64, ∀ bbits : Nat,
      HtabAligned c.KB c.BO bkeys c.SB bcap bused bvals border bop bcount bbits s → ∀ w : BitVec 64,
      TZone c.BO (min bkeys.toNat bvals.toNat) (bop.toNat + bcap.toNat * 8) w.toNat → r.memory w = s.memory w)
    (apartB : ∀ bcap bkeys bused bvals border bop bcount : BitVec 64, ∀ bbits : Nat,
      HtabAligned c.KB c.BO bkeys c.SB bcap bused bvals border bop bcount bbits s → ∀ w,
      TZone c.BO (min bkeys.toNat bvals.toNat) (bop.toNat + bcap.toNat * 8) w → ¬ c'.OFoot w)
    (apartR : ∀ b ∈ R, ∀ w, TZone b (Z b).1 (Z b).2 w → ¬ c'.OFoot w) :
    c'.CoreW IB II r p' R Z := by
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,⟨bc,bk,bu,bv,bo,bp,bn,bb,binv,bt,br,bvt,btop,bnb,bcb,bz⟩,⟨ii,io,ip⟩⟩ := core
  obtain ⟨p1,hp1,le1,al1,in1⟩ := rel.2 p a5 a7 a8
  rw [hp'] at hp1
  simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at hp1
  subst hp1
  have keepB' := keepB bc bk bu bv bo bp bn bb binv
  have K := binv.toRegions.foot_keep (r := r) (fun w h =>
    keepB' w (HtabLaid.foot_sub (Or.inl ⟨binv,rfl,rfl⟩) w.toNat h))
  refine ⟨code.trans a1,hA.symm,hBE.symm,fun w _ => by rw [hM],hp',hP,al1,in1,by rw [hG]; exact heapRel_preorder.refl _,
    ?_,?_⟩
  · unfold MergeCtx.Bouter; rw [eBO,eKB,eSB,eNB,eCB]
    exact ⟨bc,bk,bu,bv,bo,bp,bn,bb,binv.congr memaddrs be code K.1 K.2.1,
      bt.congr binv.toRegions.count_le memaddrs be K.2.1 K.2.2.1 K.2.2.2,br,
      bvt.congr binv bt memaddrs be (fun w h => keepB' w (Or.inr h)),by omega,bnb,bcb,
      fun w hz => ⟨apartB bc bk bu bv bo bp bn bb binv w hz,(bz w hz).2⟩⟩
  · unfold MergeCtx.Inners; rw [eKI,eL,eNI,eNS,eCI]
    exact ⟨fun b mem => (ii b mem).congr memaddrs be code (fun w h => keepR b mem w h) (by omega),
      fun b mem w hz => apartR b mem w hz,ip⟩

#print axioms MergeCtx.CoreW.move

/-- Any aligned reading of the block map in a state with the loop invariant has the invariant's zone: below the
heap pointer, off the outer footprint and off every registered zone. -/
theorem MergeCtx.CoreW.bzone {c : MergeCtx} {IB II : Nat} {F : Type} {s : PanSemStateFiniteExact 64 F}
    {p : BitVec 64} {R : Set (BitVec 64)} {Z : BitVec 64 → Nat × Nat} (core : c.CoreW IB II s p R Z)
    (bcap bkeys bused bvals border bop bcount : BitVec 64) (bbits : Nat)
    (inv : HtabAligned c.KB c.BO bkeys c.SB bcap bused bvals border bop bcount bbits s) (w : Nat)
    (hz : TZone c.BO (min bkeys.toNat bvals.toNat) (bop.toNat + bcap.toNat * 8) w) :
    w < p.toNat ∧ ¬ c.OFoot w ∧ ∀ b ∈ R, ¬ TZone b (Z b).1 (Z b).2 w := by
  obtain ⟨_,_,_,_,_,_,_,_,_,⟨bc,bk,bu,bv,bo,bp,bn,bb,binv,_,_,_,btop,_,_,bz⟩,_⟩ := core
  obtain ⟨e1,e2,_,e4,_,e6,_,_⟩ := HtabAligned.unique binv inv
  rw [e1,e2,e4,e6] at hz
  exact ⟨MergeCtx.Bouter.zone_below bc bk bu bv bo bp bn bb binv btop w hz,bz w hz⟩

#print axioms MergeCtx.CoreW.bzone

theorem MergeCtx.SrcTab.widen {c c' : MergeCtx} {F : Type} {s : PanSemStateFiniteExact 64 F} {v : BitVec 64}
    (t : c.SrcTab s v) (eNS : c'.NS = c.NS) (sub : ∀ w, c.OFoot w → c'.OFoot w) : c'.SrcTab s v := by
  obtain ⟨skl,skeys,sstride,scap,sused,svals,sorder,sorderPos,sn,sbits,sinv,stables,snB,foot⟩ := t
  exact ⟨skl,skeys,sstride,scap,sused,svals,sorder,sorderPos,sn,sbits,sinv,stables,by rw [eNS]; exact snB,
    fun w h => sub w (foot w h)⟩

/-- Storage-side entry data of `merge_tx_into_block` at its entry state `s`: a storage-loop context whose entry
data is `s` and whose heap baseline `P0` is the entry heap pointer, the loop invariant there, the outer map with
its record cells inside the outer footprint, and every storage-side word apart from the five union zones. -/
structure MergeStoreEntry (B T : BitVec 64) (ps : List UnionPair) {F : Type} (s : PanSemStateFiniteExact 64 F)
    (c : MergeCtx) (R : Set (BitVec 64)) (Z : BitVec 64 → Nat × Nat) : Prop where
  m0 : c.M0 = s.memory
  a0 : c.A0 = s.memaddrs
  be0 : c.BE = s.be
  g0 : c.G0 = s.globals
  st : c.Static
  bd : c.BoundsK
  core : c.CoreW 0 0 s c.P0 R Z
  outer : c.OuterOK s
  dO : s.memaddrs (T + 32)
  cO : s.memory (T + 32) = .word c.O
  fO : c.OFoot (T + 32).toNat
  dBO : s.memaddrs (B + 32)
  cBO : s.memory (B + 32) = .word c.BO
  fBO : c.OFoot (B + 32).toNat
  dn : s.memaddrs (c.O + 24)
  cn : s.memory (c.O + 24) = .word c.n
  fn : c.OFoot (c.O + 24).toNat
  apartO : ∀ w, c.OFoot w → ∀ q ∈ ps, ¬ q.Zone w
  apartB : ∀ bcap bkeys bused bvals border bop bcount : BitVec 64, ∀ bbits : Nat,
    HtabAligned c.KB c.BO bkeys c.SB bcap bused bvals border bop bcount bbits s → ∀ w,
    TZone c.BO (min bkeys.toNat bvals.toNat) (bop.toNat + bcap.toNat * 8) w → ∀ q ∈ ps, ¬ q.Zone w
  apartR : ∀ b ∈ R, ∀ w, TZone b (Z b).1 (Z b).2 w → ∀ q ∈ ps, ¬ q.Zone w

/-- The storage-loop context after the five unions: entry data from the mid state, heap baseline the mid heap
pointer, and an outer footprint extended by the union zones and the words allocated during the unions. -/
def MergeCtx.afterUnions (c : MergeCtx) (ps : List UnionPair) {F : Type} (mid : PanSemStateFiniteExact 64 F)
    (pm : BitVec 64) : MergeCtx :=
  ⟨c.O,c.n,c.okeys,c.ostride,c.ovals,c.oorder,c.BO,c.KB,c.SB,c.KI,c.SI,pm,c.L,c.NB0,c.CB,c.NI0,c.CI,c.NS,
    mid.memory,mid.memaddrs,mid.be,mid.globals,fun w => c.OFoot w ∨ (∃ q ∈ ps, q.Zone w) ∨ (c.P0.toNat ≤ w ∧ w < pm.toNat)⟩

set_option maxHeartbeats 4000000 in
/-- `merge_tx_into_block` returning: the five unions (o = 24, 8, 40, 16, 48) followed by the clamped storage
loop. It returns 0, each union destination ends as described by `Done`, the outer footprint is unchanged, and the
storage-loop invariant holds at return for a context with the same tables and parameters. -/
theorem merge_tx_into_block_returned (B T : BitVec 64) (ps : List UnionPair)
    (offsets : ps.map UnionPair.o = [24,8,40,16,48]) {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64) (c : MergeCtx) (R : Set (BitVec 64)) (Z : BitVec 64 → Nat × Nat)
    (hB : s.globals.lookup (ofString "bs") = some (.val (.word B)))
    (hT : s.globals.lookup (ofString "ts") = some (.val (.word T)))
    (ready : ∀ q ∈ ps, q.Ready B T s ∧ q.Placed B T c.P0) (apart : ps.Pairwise (UnionPair.Apart B T))
    (entry : MergeStoreEntry B T ps s c R Z)
    (budget : (ps.map UnionPair.cost).sum + c.n.toNat * (c.iterCostK + 1) ≤ s.clock)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_merge_tx_into_block) = (some (.returned v),post)) :
    v = .val (.word 0) ∧ (∀ q ∈ ps, q.Done c.P0 post) ∧
      (∀ w : BitVec 64, c.OFoot w.toNat → post.memory w = s.memory w) ∧
      post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ post.be = s.be ∧ HeapRel s.globals post.globals ∧
      ∃ c' : MergeCtx, c'.BO = c.BO ∧ c'.KB = c.KB ∧ c'.SB = c.SB ∧ c'.KI = c.KI ∧ c'.L = c.L ∧ c'.NB0 = c.NB0 ∧
        c'.CB = c.CB ∧ c'.NI0 = c.NI0 ∧ c'.CI = c.CI ∧ c'.NS = c.NS ∧ c'.n = c.n ∧
        (∀ w, c.OFoot w → c'.OFoot w) ∧ ∃ p R' Z', c'.CoreW c.n.toNat c.n.toNat post p R' Z' := by
  have core := entry.core
  have st := entry.st
  obtain ⟨cc,_,_,_,hp0,_,al0,in0,_,_,inn⟩ := core
  obtain ⟨mid,midRun,mc,ma,mb,_,mrel,mclk,mframe,mdone⟩ :=
    merge_unions_returned B T c.P0 ps offsets s post v cc hB hT ⟨c.P0,hp0,le_refl _,al0,in0⟩ ready apart
      (by omega) run
  obtain ⟨pm,hpm,lepm,alpm,inpm⟩ := mrel.2 c.P0 hp0 al0 in0
  have kept : ∀ w : BitVec 64, w.toNat < c.P0.toNat → (∀ q ∈ ps, ¬ q.Zone w.toNat) → mid.memory w = s.memory w :=
    mframe c.P0 hp0
  have kO : ∀ w : BitVec 64, c.OFoot w.toNat → mid.memory w = s.memory w := fun w h =>
    kept w (st.ofBelow _ h) (entry.apartO _ h)
  have st' : (c.afterUnions ps mid pm).Static := by
    refine ⟨st.kI,Nat.le_trans st.LP lepm,st.LB,st.ci8,?_,?_,st.kbSmall,st.ciSmall,st.cbSmall⟩
    · rintro w (h | ⟨q,mem,hz⟩ | ⟨_,h⟩)
      · have := st.ofBelow w h; exact Nat.lt_of_lt_of_le this lepm
      · have := (ready q mem).2.1 w (Or.inl hz); exact Nat.lt_of_lt_of_le this lepm
      · exact h
    · intro a h1 h2 h3; show mid.memaddrs a; rw [ma,← entry.a0]; exact st.arena a h1 h2 h3
  have core' : (c.afterUnions ps mid pm).CoreW 0 0 mid pm R Z :=
    entry.core.move ma mb mc mrel pm hpm rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (le_refl _)
      (fun b mem w hz => kept w ((inn.1 b mem).zone_below w.toNat hz) (entry.apartR b mem w.toNat hz))
      (fun bc bk bu bv bo bp bn bb inv w hz => kept w (entry.core.bzone bc bk bu bv bo bp bn bb inv w.toNat hz).1
        (entry.apartB bc bk bu bv bo bp bn bb inv w.toNat hz))
      (fun bc bk bu bv bo bp bn bb inv w hz => by
        obtain ⟨lt,nO,_⟩ := entry.core.bzone bc bk bu bv bo bp bn bb inv w hz
        rintro (h | ⟨q,mem,hq⟩ | ⟨h,_⟩)
        · exact nO h
        · exact entry.apartB bc bk bu bv bo bp bn bb inv w hz q mem hq
        · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le lt h))
      (fun b mem w hz => by
        have lt := (inn.1 b mem).zone_below w hz
        rintro (h | ⟨q,mem',hq⟩ | ⟨h,_⟩)
        · exact inn.2.1 b mem w hz h
        · exact entry.apartR b mem w hz q mem' hq
        · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le lt h))
  have sub : ∀ w, c.OFoot w → (c.afterUnions ps mid pm).OFoot w := fun w h => Or.inl h
  have outer' : (c.afterUnions ps mid pm).OuterOK mid := by
    unfold MergeCtx.OuterOK; dsimp only [MergeCtx.afterUnions]
    obtain ⟨⟨d1,e1,f1⟩,⟨d2,e2,f2⟩,⟨d3,e3,f3⟩,⟨d4,e4,f4⟩,items⟩ := entry.outer
    refine ⟨⟨by rw [ma]; exact d1,by rw [kO _ f1]; exact e1,sub _ f1⟩,⟨by rw [ma]; exact d2,by rw [kO _ f2]; exact e2,
      sub _ f2⟩,⟨by rw [ma]; exact d3,by rw [kO _ f3]; exact e3,sub _ f3⟩,⟨by rw [ma]; exact d4,by rw [kO _ f4]; exact e4,
      sub _ f4⟩,fun k hk => ?_⟩
    obtain ⟨slot,u,a1,a2,a3,a4,a5,a6,t⟩ := items k hk
    exact ⟨slot,u,by rw [ma]; exact a1,by rw [kO _ a3]; exact a2,sub _ a3,by rw [ma]; exact a4,by rw [kO _ a6]; exact a5,
      sub _ a6,(t.move ma mb mc kO).widen (c' := c.afterUnions ps mid pm) rfl sub⟩
  have glob : ∀ name, name ≠ ofString "heap_ptr" → mid.globals.lookup name = s.globals.lookup name := mrel.1
  have cost : (c.afterUnions ps mid pm).iterCostK = c.iterCostK := rfl
  have nEq : (c.afterUnions ps mid pm).n = c.n := rfl
  have bd' : (c.afterUnions ps mid pm).BoundsK := by
    obtain ⟨b1,b2,b3,b4,b5,b6⟩ := entry.bd; exact ⟨b1,b2,b3,b4,b5,b6⟩
  obtain ⟨ve,p'',R'',Z'',core''⟩ := mergeTail_returnedK st' bd' mid post v T B
    (by rw [glob _ (by decide)]; exact hT) (by rw [glob _ (by decide)]; exact hB)
    (by rw [ma]; exact entry.dO) (by rw [kO _ entry.fO]; exact entry.cO)
    (by rw [ma]; exact entry.dBO) (by rw [kO _ entry.fBO]; exact entry.cBO)
    (by show mid.memaddrs (c.O + 24); rw [ma]; exact entry.dn)
    (by show mid.memory (c.O + 24) = .word c.n; rw [kO _ entry.fn]; exact entry.cn) pm R Z core' outer'
    (by rw [cost,nEq]; omega) (by rw [← mergeTail_eq]; exact midRun)
  have core3 := core''
  obtain ⟨pc,pa,pbe,pkeep,phe,pP0,_,_,prel,_,_⟩ := core3
  change post.memaddrs = mid.memaddrs at pa
  change post.be = mid.be at pbe
  change pm.toNat ≤ p''.toNat at pP0
  change HeapRel mid.globals post.globals at prel
  have pkeep' : ∀ w : BitVec 64, (c.afterUnions ps mid pm).OFoot w.toNat → post.memory w = mid.memory w := pkeep
  refine ⟨ve,fun q mem => ?_,fun w h => by rw [pkeep' w (sub _ h),kO w h],pc.trans cc.symm,pa.trans ma,
    pbe.trans mb,heapRel_preorder.trans _ _ _ mrel prel,
    c.afterUnions ps mid pm,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,sub,p'',R'',Z'',core''⟩
  obtain ⟨cap,keys,used,values,order,orderPos,count,bits,lo,hi,laid,tables,r1,r2,r3,r4,r5⟩ := mdone q mem
  have incl : ∀ w, TZone q.dst lo hi w → (c.afterUnions ps mid pm).OFoot w := by
    intro w hz
    rcases hz with hh | hl
    · exact Or.inr (Or.inl ⟨q,mem,Or.inl hh⟩)
    · rcases r5 with ⟨rfl,rfl⟩ | ⟨lp,p2,hp2,le2⟩
      · exact Or.inr (Or.inl ⟨q,mem,Or.inr hl⟩)
      · rw [hpm] at hp2
        simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at hp2
        subst hp2
        exact Or.inr (Or.inr ⟨by omega,by omega⟩)
  obtain ⟨laid',tables'⟩ := laid.congr_tables tables pa pbe (pc.trans (mc.trans cc).symm)
    (fun w h => pkeep' w (incl _ (laid.foot_sub w.toNat h)))
  refine ⟨cap,keys,used,values,order,orderPos,count,bits,lo,hi,laid',tables',r1,r2,r3,r4,?_⟩
  rcases r5 with h | ⟨lp,p2,hp2,le2⟩
  · exact Or.inl h
  · rw [hpm] at hp2
    simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at hp2
    subst hp2
    exact Or.inr ⟨lp,p'',phe,by omega⟩

#print axioms merge_tx_into_block_returned
end InitECandidate.Runtime
