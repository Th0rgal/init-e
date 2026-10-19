import InitECandidate.Runtime.HtabMergeWhole
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 4000000 in
/-- All-outcome bound for a chain of `htab_union_into(lds(bs+o), lds(ts+o))` calls on ready, placed, pairwise
apart table pairs, followed by `rest`: each call costs its pair's bound, and `rest` is only needed from states
reached after every call returned normally, which keep code, addresses, endianness and locals, extend the heap,
keep every word below the entry heap pointer outside the destination zones, and leave each destination `Done`. -/
theorem unionChain_bounded (B T P0 : BitVec 64) (rest : ProgHOL 64) (restCost : Nat) :
    ∀ (ps : List UnionPair) {F : Type} (s : PanSemStateFiniteExact 64 F),
      s.code = originalRuntimeCode →
      s.globals.lookup (ofString "bs") = some (.val (.word B)) →
      s.globals.lookup (ofString "ts") = some (.val (.word T)) →
      (∃ p : BitVec 64, s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) ∧ P0.toNat ≤ p.toNat ∧
        p.toNat % 8 = 0 ∧ p.toNat ≤ 33806089496) →
      (∀ q ∈ ps, q.Ready B T s ∧ q.Placed B T P0) →
      ps.Pairwise (UnionPair.Apart B T) →
      (∀ mid : PanSemStateFiniteExact 64 F, mid.code = s.code → mid.memaddrs = s.memaddrs → mid.be = s.be →
        mid.locals = s.locals → HeapRel s.globals mid.globals →
        (∀ p : BitVec 64, s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) → ∀ w : BitVec 64,
          w.toNat < p.toNat → (∀ q ∈ ps, ¬ q.Zone w.toNat) → mid.memory w = s.memory w) →
        (∀ q ∈ ps, q.Done P0 mid) → restCost ≤ mid.clock → RunBounded mid rest restCost) →
      (ps.map UnionPair.cost).sum + restCost ≤ s.clock →
      RunBounded s (unionChain (ps.map UnionPair.o) rest) ((ps.map UnionPair.cost).sum + restCost) := by
  intro ps
  induction ps with
  | nil =>
    intro F s _ _ _ _ _ _ tailB budget
    simp only [List.map_nil,unionChain,List.sum_nil,Nat.zero_add] at budget ⊢
    exact tailB s rfl rfl rfl rfl (heapRel_preorder.refl _) (fun _ _ _ _ _ => rfl) (by simp) budget
  | cons q qs ih =>
    intro F s code hB hT ⟨p,hp,pP0,pal,pin⟩ ready apart tailB budget
    simp only [List.map_cons,unionChain,List.sum_cons] at budget ⊢
    rw [Nat.add_assoc]
    obtain ⟨⟨⟨dB,cB⟩,⟨dT,cT⟩,laid,tables,room,sinv,stables,arena⟩,footBelow,srcOwn,small⟩ := ready q List.mem_cons_self
    obtain ⟨apartHead,apartTail⟩ := List.pairwise_cons.mp apart
    have args := union_record_args s .global .global (ofString "bs") (ofString "ts") B T q.o q.o q.dst q.src
      (eval_global_word s _ B hB) (eval_global_word s _ T hT) dB cB dT cT
    have hdr : q.dst.toNat + 72 ≤ P0.toNat := by
      have := footBelow (q.dst.toNat + 71) (Or.inl (Or.inl ⟨by omega,by omega⟩)); omega
    have away : ∀ w : BitVec 64, ((q.src.toNat ≤ w.toNat ∧ w.toNat < q.src.toNat + 72) ∨
        (q.sorder.toNat ≤ w.toNat ∧ w.toNat < q.sorder.toNat + q.scap.toNat * 8) ∨
        (q.svalues.toNat ≤ w.toNat ∧ w.toNat < q.svalues.toNat + q.scap.toNat * 8)) →
        w.toNat < p.toNat ∧ (w.toNat < q.dst.toNat ∨ q.dst.toNat + 72 ≤ w.toNat) ∧ (w.toNat < q.lo ∨ q.hi ≤ w.toNat) :=
      fun w h => by
        have b := footBelow w.toNat (Or.inr (Or.inr (Or.inl h)))
        have z := q.not_zone _ (srcOwn w.toNat h)
        exact ⟨by omega,z.1,z.2⟩
    have left := runBounded_union_tables s _ _ q.keyLength q.dst q.keys q.stride q.capacity q.used q.values q.order
      q.orderPos q.count q.bits q.lo q.hi laid tables room q.src q.skl q.skeys q.sstride q.scap q.sused q.svalues q.sorder
      q.sorderPos q.n q.sbits sinv stables args p hp pal pin (by omega) arena small away
      (by rw [UnionPair.cost_eq]; omega)
    rw [UnionPair.cost_eq] at left
    refine RunBounded.seq left (by omega) (fun s1 callRun _ clk1 => ?_)
    obtain ⟨D,⟨⟨p1,hp1,pp1,pal1,pin1⟩,rel1⟩,L,A,Be,C,Fr,Clk⟩ := htabUnionInto_tables_callT s s1 _ _ q.keyLength q.dst
      q.keys q.stride q.capacity q.used q.values q.order q.orderPos q.count q.bits q.lo q.hi laid tables room q.src q.skl
      q.skeys q.sstride q.scap q.sused q.svalues q.sorder q.sorderPos q.n q.sbits sinv stables args p hp pal pin
      (by omega) arena small away (by rw [UnionPair.cost_eq]; omega) callRun
    have kept : ∀ w : BitVec 64, w.toNat < p.toNat → ¬ q.Zone w.toNat → s1.memory w = s.memory w := by
      intro w wlt nz
      have z := q.not_zone _ nz
      exact Fr w ⟨wlt,z.1,z.2⟩
    have readyTail : ∀ k ∈ qs, k.Ready B T s1 ∧ k.Placed B T P0 := by
      intro k mem
      obtain ⟨kr,kp⟩ := ready k (List.mem_cons_of_mem _ mem)
      refine ⟨k.ready_keep B T kr A Be C (fun w h => kept w ?_ ((apartHead k mem).2 _ h)),kp⟩
      have := kp.1 _ h; omega
    have glob : ∀ name, name ≠ ofString "heap_ptr" → s1.globals.lookup name = s.globals.lookup name := rel1.1
    refine ih s1 (C.trans code) (by rw [glob _ (by decide)]; exact hB) (by rw [glob _ (by decide)]; exact hT)
      ⟨p1,hp1,by change p.toNat ≤ p1.toNat at pp1; omega,pal1,pin1⟩ readyTail apartTail ?_ clk1
    intro mid mc ma mb ml mrel mframe mdone mclk
    refine tailB mid (mc.trans C) (ma.trans A) (mb.trans Be) (ml.trans L) (heapRel_preorder.trans _ _ _ rel1 mrel) ?_ ?_ mclk
    · intro p' hp' w wlt nz
      rw [hp] at hp'
      simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at hp'
      subst hp'
      rw [mframe p1 hp1 w (by change p.toNat ≤ p1.toNat at pp1; omega)
        (fun k mem => nz k (List.mem_cons_of_mem _ mem)),kept w wlt (nz q List.mem_cons_self)]
    · intro k mem
      rcases List.mem_cons.mp mem with rfl | inTail
      · obtain ⟨c',k',u',v',o',op',n',b',lo',hi',laid',tables',r1,r2,r3,r4,r5⟩ := D
        have keepNew : ∀ w : BitVec 64, HtabFoot k.dst c' u' o' op' w.toNat → mid.memory w = s1.memory w := by
          intro w h
          rcases laid'.foot_sub w.toNat h with hd | blk
          · have inZ : k.Zone w.toNat := Or.inl hd
            have := footBelow _ (Or.inl inZ)
            exact mframe p1 hp1 w (by change p.toNat ≤ p1.toNat at pp1; omega)
              (fun j jm => (apartHead j jm).1 _ (Or.inl inZ))
          · rcases r5 with ⟨rfl,rfl⟩ | ⟨lp,p2,hp2,le2⟩
            · have inZ : k.Zone w.toNat := Or.inr blk
              have := footBelow _ (Or.inl inZ)
              exact mframe p1 hp1 w (by change p.toNat ≤ p1.toNat at pp1; omega)
                (fun j jm => (apartHead j jm).1 _ (Or.inl inZ))
            · rw [hp1] at hp2
              simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at hp2
              subst hp2
              change p.toNat ≤ lo' at lp
              refine mframe p1 hp1 w (by omega) (fun j jm hz => ?_)
              have := (readyTail j jm).2.1 _ (Or.inl hz)
              omega
        obtain ⟨laidM,tablesM⟩ := laid'.congr_tables tables' ma mb mc keepNew
        refine ⟨c',k',u',v',o',op',n',b',lo',hi',laidM,tablesM,r1,r2,r3,r4,?_⟩
        rcases r5 with h | ⟨lp,p2,hp2,le2⟩
        · exact Or.inl h
        · rw [hp1] at hp2
          simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at hp2
          subst hp2
          obtain ⟨p3,hp3,le3,_,_⟩ := mrel.2 p1 hp1 pal1 pin1
          change p.toNat ≤ lo' at lp
          exact Or.inr ⟨by omega,p3,hp3,by omega⟩
      · exact mdone k inTail

#print axioms unionChain_bounded

set_option maxHeartbeats 4000000 in
/-- All-outcome bound for the complete original `merge_tx_into_block`: the five unions (o = 24, 8, 40, 16, 48),
each within its pair's bound, then the clamped storage loop within `n * (iterCostK + 1)`, from the same entry
premises as `merge_tx_into_block_returned`. -/
theorem runBounded_merge_tx_into_block (B T : BitVec 64) (ps : List UnionPair)
    (offsets : ps.map UnionPair.o = [24,8,40,16,48]) {F : Type} (s : PanSemStateFiniteExact 64 F)
    (c : MergeCtx) (R : Set (BitVec 64)) (Z : BitVec 64 → Nat × Nat)
    (hB : s.globals.lookup (ofString "bs") = some (.val (.word B)))
    (hT : s.globals.lookup (ofString "ts") = some (.val (.word T)))
    (ready : ∀ q ∈ ps, q.Ready B T s ∧ q.Placed B T c.P0) (apart : ps.Pairwise (UnionPair.Apart B T))
    (entry : MergeStoreEntry B T ps s c R Z)
    (budget : (ps.map UnionPair.cost).sum + c.n.toNat * (c.iterCostK + 1) ≤ s.clock) :
    RunBounded s (sourceFunctionBody Guest.guestFn_merge_tx_into_block)
      ((ps.map UnionPair.cost).sum + (c.n.toNat * (c.iterCostK + 1) + 0)) := by
  have core := entry.core
  have st := entry.st
  obtain ⟨cc,_,_,_,hp0,_,al0,in0,_,_,inn⟩ := core
  rw [source_merge_body,← offsets]
  refine unionChain_bounded B T c.P0 mergeTail _ ps s cc hB hT ⟨c.P0,hp0,le_refl _,al0,in0⟩ ready apart ?_ (by omega)
  intro mid mc ma mb _ mrel mframe _ mclk
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
  rw [mergeTail_eq]
  have bound := runBounded_mergeTailK st' bd' mid T B
    (by rw [glob _ (by decide)]; exact hT) (by rw [glob _ (by decide)]; exact hB)
    (by rw [ma]; exact entry.dO) (by rw [kO _ entry.fO]; exact entry.cO)
    (by rw [ma]; exact entry.dBO) (by rw [kO _ entry.fBO]; exact entry.cBO)
    (by show mid.memaddrs (c.O + 24); rw [ma]; exact entry.dn)
    (by show mid.memory (c.O + 24) = .word c.n; rw [kO _ entry.fn]; exact entry.cn) pm R Z core' outer'
    (by rw [cost,nEq]; omega)
  rw [cost,nEq] at bound
  exact bound

#print axioms runBounded_merge_tx_into_block
end InitECandidate.Runtime
