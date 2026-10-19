import InitECandidate.Runtime.HtabUnionTop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-! The union call sites from table invariants: the five `htab_union_into(lds(bs+o), lds(ts+o))`
calls opening `merge_tx_into_block`, composed over ready, placed, pairwise apart table pairs
(`unionChain_returned`, `merge_unions_returned`), and the call in `incorporate_child_on_success`
(`incorporate_union_call`). -/

/-- The footprint a laid-out table's invariant reads lies in its header or its array block. -/
theorem HtabLaid.foot_sub {F : Type} {s : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat} {lo hi : Nat}
    (laid : HtabLaid keyLength table keys stride capacity used values order orderPos count bits lo hi s) (w : Nat)
    (h : HtabFoot table capacity used order orderPos w) :
    (table.toNat ≤ w ∧ w < table.toNat + 72) ∨ (lo ≤ w ∧ w < hi) := by
  unfold HtabFoot at h
  rcases laid with ⟨inv,rfl,rfl⟩ | ⟨inv,rfl,rfl⟩
  · have := inv.keysBefore; have := inv.valuesBefore; have := inv.usedBefore; have := inv.orderBefore
    have : keys.toNat ≤ keys.toNat + capacity.toNat * stride.toNat := Nat.le_add_right _ _
    have : min keys.toNat values.toNat ≤ keys.toNat := Nat.min_le_left _ _
    rcases h with h | h | h | h <;> omega
  · have := inv.keysBelow; have := inv.valuesBelow; have := inv.usedBelow; have := inv.orderBelow
    have := inv.orderPosBelow
    have : keys.toNat ≤ keys.toNat + capacity.toNat * stride.toNat := Nat.le_add_right _ _
    rcases h with h | h | h | h <;> omega

#print axioms HtabLaid.foot_sub

/-- The table-level union call with the heap-placement clause and its clock bound. -/
theorem htabUnionInto_tables_callT {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (dstArgument srcArgument : ExpHOL 64)
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
      lo hi state).stepCost + 1) + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_union_into") [dstArgument,srcArgument]) =
      (none,post)) :
    (unionCtxOf keyLength dst stride src n skeys sstride svalues sorder count capacity pointer lo hi state).DstT n post ∧
      (unionCtxOf keyLength dst stride src n skeys sstride svalues sorder count capacity pointer lo hi state).Heap post ∧
      post.locals = state.locals ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ post.code = state.code ∧
      (∀ w, (unionCtxOf keyLength dst stride src n skeys sstride svalues sorder count capacity pointer lo hi state).Away w →
        post.memory w = state.memory w) ∧
      state.clock ≤ post.clock + (n.toNat * ((unionCtxOf keyLength dst stride src n skeys sstride svalues sorder count
        capacity pointer lo hi state).stepCost + 1) + 1) := by
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
  obtain ⟨d1,d2,d3,d4,d5,d6,d7⟩ := htabUnionInto_call_normalT _ ok reads state post dstArgument srcArgument laid.code args
    (sinv.header_domain 24 (by omega) (by omega)) sinv.cell24 rfl rfl rfl
    ⟨keys,used,values,order,orderPos,bits,laid,tables⟩ heap budget run
  have rb := runBounded_htabUnionInto_callT _ ok reads state none dstArgument srcArgument laid.code args
    (sinv.header_domain 24 (by omega) (by omega)) sinv.cell24 rfl rfl rfl
    ⟨keys,used,values,order,orderPos,bits,laid,tables⟩ heap budget
  unfold RunBounded at rb
  rw [run] at rb
  exact ⟨d1,d2,d3,d4,d5,d6,d7,rb.1⟩

#print axioms htabUnionInto_tables_callT

def mergeUnionCall (o : BitVec 64) : ProgHOL 64 :=
  .call (some (none,none)) (ofString "htab_union_into")
    [.load .one (.op .add [.var .global (ofString "bs"),.const o]),.load .one (.op .add [.var .global (ofString "ts"),.const o])]

def unionChain : List (BitVec 64) → ProgHOL 64 → ProgHOL 64
  | [], rest => rest
  | o :: os, rest => .seq (mergeUnionCall o) (unionChain os rest)

theorem source_merge_unions : ∃ tail : ProgHOL 64,
    sourceFunctionBody Guest.guestFn_merge_tx_into_block = unionChain [24,8,40,16,48] tail := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  exact ⟨_,rfl⟩


/-- One `htab_union_into(lds(bs+o), lds(ts+o))` call: record offset, destination and source tables. -/
structure UnionPair where
  o : BitVec 64
  keyLength : BitVec 64
  dst : BitVec 64
  keys : BitVec 64
  stride : BitVec 64
  capacity : BitVec 64
  used : BitVec 64
  values : BitVec 64
  order : BitVec 64
  orderPos : BitVec 64
  count : BitVec 64
  bits : Nat
  lo : Nat
  hi : Nat
  src : BitVec 64
  skl : BitVec 64
  skeys : BitVec 64
  sstride : BitVec 64
  scap : BitVec 64
  sused : BitVec 64
  svalues : BitVec 64
  sorder : BitVec 64
  sorderPos : BitVec 64
  n : BitVec 64
  sbits : Nat

/-- The destination header and array block. -/
def UnionPair.Zone (q : UnionPair) (w : Nat) : Prop :=
  (q.dst.toNat ≤ w ∧ w < q.dst.toNat + 72) ∨ (q.lo ≤ w ∧ w < q.hi)

/-- The source reads: header, order array and value array. -/
def UnionPair.SrcRead (q : UnionPair) (w : Nat) : Prop :=
  (q.src.toNat ≤ w ∧ w < q.src.toNat + 72) ∨ (q.sorder.toNat ≤ w ∧ w < q.sorder.toNat + q.scap.toNat * 8) ∨
    (q.svalues.toNat ≤ w ∧ w < q.svalues.toNat + q.scap.toNat * 8)

/-- Every word the pair's call reads or relies on. -/
def UnionPair.Foot (q : UnionPair) (B T : BitVec 64) (w : Nat) : Prop :=
  q.Zone w ∨ HtabFoot q.src q.scap q.sused q.sorder q.sorderPos w ∨ q.SrcRead w ∨
    w = (B + q.o).toNat ∨ w = (T + q.o).toNat

/-- The pair's tables and records in state s. -/
def UnionPair.Ready (q : UnionPair) (B T : BitVec 64) {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  (s.memaddrs (B + q.o) ∧ s.memory (B + q.o) = .word q.dst) ∧ (s.memaddrs (T + q.o) ∧ s.memory (T + q.o) = .word q.src) ∧
  HtabLaid q.keyLength q.dst q.keys q.stride q.capacity q.used q.values q.order q.orderPos q.count q.bits q.lo q.hi s ∧
  OrderInv s q.capacity q.count q.used q.order q.orderPos ∧ q.count.toNat < q.capacity.toNat ∧
  HtabRegions q.skl q.src q.skeys q.sstride q.scap q.sused q.svalues q.sorder q.sorderPos q.n q.sbits s ∧
  OrderInv s q.scap q.n q.sused q.sorder q.sorderPos ∧
  (∀ a : BitVec 64, a.toNat % 8 = 0 → q.dst.toNat ≤ a.toNat → a.toNat < 33806089496 → s.memaddrs a)

/-- Static placement: everything lies below P0 and the source reads avoid the pair's own zone. -/
def UnionPair.Placed (q : UnionPair) (B T P0 : BitVec 64) : Prop :=
  (∀ w, q.Foot B T w → w < P0.toNat) ∧ (∀ w, q.SrcRead w → ¬ q.Zone w) ∧ q.keyLength.toNat ≤ 33806089496

/-- Pairwise: neither pair's footprint meets the other's zone. -/
def UnionPair.Apart (B T : BitVec 64) (p q : UnionPair) : Prop :=
  (∀ w, p.Foot B T w → ¬ q.Zone w) ∧ (∀ w, q.Foot B T w → ¬ p.Zone w)

def UnionPair.ctx (q : UnionPair) : UnionCtx :=
  ⟨q.keyLength,q.dst,q.stride,q.src,q.n,q.skeys,q.sstride,q.svalues,q.sorder,q.count,q.capacity,0,q.lo,q.hi,
    fun _ => .word 0,fun _ => True,HolFiniteMapExact.empty⟩

def UnionPair.cost (q : UnionPair) : Nat := q.n.toNat * (q.ctx.stepCost + 1) + 1

/-- The pair's destination after the chain. -/
def UnionPair.Done (q : UnionPair) (P0 : BitVec 64) {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ (capacity keys used values order orderPos count : BitVec 64) (bits lo hi : Nat),
    HtabLaid q.keyLength q.dst keys q.stride capacity used values order orderPos count bits lo hi s ∧
    OrderInv s capacity count used order orderPos ∧ count.toNat < capacity.toNat ∧
    q.count.toNat ≤ count.toNat ∧ count.toNat ≤ q.count.toNat + q.n.toNat ∧
    (capacity.toNat ≤ q.capacity.toNat ∨ capacity.toNat ≤ 4 * count.toNat) ∧
    ((lo = q.lo ∧ hi = q.hi) ∨ (P0.toNat ≤ lo ∧ ∃ p : BitVec 64,
      s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) ∧ hi ≤ p.toNat))


theorem UnionPair.not_zone (q : UnionPair) (w : Nat) (h : ¬ q.Zone w) :
    (w < q.dst.toNat ∨ q.dst.toNat + 72 ≤ w) ∧ (w < q.lo ∨ q.hi ≤ w) := by
  unfold UnionPair.Zone at h
  constructor
  · by_cases a : q.dst.toNat ≤ w
    · right; by_contra b; exact h (Or.inl ⟨a,by omega⟩)
    · left; omega
  · by_cases a : q.lo ≤ w
    · right; by_contra b; exact h (Or.inr ⟨a,by omega⟩)
    · left; omega

theorem UnionPair.ready_keep (q : UnionPair) (B T : BitVec 64) {F : Type} {s r : PanSemStateFiniteExact 64 F}
    (ready : q.Ready B T s) (memaddrs : r.memaddrs = s.memaddrs) (be : r.be = s.be) (code : r.code = s.code)
    (keep : ∀ w : BitVec 64, q.Foot B T w.toNat → r.memory w = s.memory w) : q.Ready B T r := by
  obtain ⟨⟨dB,cB⟩,⟨dT,cT⟩,laid,tables,room,sinv,stables,arena⟩ := ready
  obtain ⟨laid',tables'⟩ := laid.congr_tables tables memaddrs be code (fun w h =>
    keep w (Or.inl (laid.foot_sub w.toNat h)))
  have sK := sinv.foot_keep (r := r) (fun w h => keep w (Or.inr (Or.inl h)))
  refine ⟨⟨by rw [memaddrs]; exact dB,by rw [keep _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact cB⟩,
    ⟨by rw [memaddrs]; exact dT,by rw [keep _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]; exact cT⟩,laid',tables',room,
    sinv.congr memaddrs be code (fun w h => keep w (Or.inr (Or.inl h))),
    stables.congr sinv.count_le memaddrs be sK.2.1 sK.2.2.1 sK.2.2.2,fun a h1 h2 h3 => by rw [memaddrs]; exact arena a h1 h2 h3⟩

#print axioms UnionPair.ready_keep

theorem UnionPair.cost_eq (q : UnionPair) {F : Type} (p : BitVec 64) (s : PanSemStateFiniteExact 64 F) :
    q.n.toNat * ((unionCtxOf q.keyLength q.dst q.stride q.src q.n q.skeys q.sstride q.svalues q.sorder q.count q.capacity
      p q.lo q.hi s).stepCost + 1) + 1 = q.cost := rfl

set_option maxHeartbeats 2000000 in
/-- A chain of `htab_union_into(lds(bs+o), lds(ts+o))` calls on ready, placed, pairwise apart table
pairs: each destination ends laid out (initial block, or a fresh block at or above P0 ending at or below
the heap pointer), and every word below the entry heap pointer outside all destination zones is kept. -/
theorem unionChain_returned (B T P0 : BitVec 64) :
    ∀ (ps : List UnionPair) {F : Type} (s post : PanSemStateFiniteExact 64 F) (rest : ProgHOL 64) (v : ValueHOL 64),
      s.code = originalRuntimeCode →
      s.globals.lookup (ofString "bs") = some (.val (.word B)) →
      s.globals.lookup (ofString "ts") = some (.val (.word T)) →
      (∃ p : BitVec 64, s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) ∧ P0.toNat ≤ p.toNat ∧
        p.toNat % 8 = 0 ∧ p.toNat ≤ 33806089496) →
      (∀ q ∈ ps, q.Ready B T s ∧ q.Placed B T P0) →
      ps.Pairwise (UnionPair.Apart B T) →
      (ps.map UnionPair.cost).sum ≤ s.clock →
      evaluateHOLFiniteState s (unionChain (ps.map UnionPair.o) rest) = (some (.returned v),post) →
      ∃ mid : PanSemStateFiniteExact 64 F,
        evaluateHOLFiniteState mid rest = (some (.returned v),post) ∧
        mid.code = s.code ∧ mid.memaddrs = s.memaddrs ∧ mid.be = s.be ∧ mid.locals = s.locals ∧
        HeapRel s.globals mid.globals ∧ s.clock ≤ mid.clock + (ps.map UnionPair.cost).sum ∧
        (∀ p : BitVec 64, s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) → ∀ w : BitVec 64,
          w.toNat < p.toNat → (∀ q ∈ ps, ¬ q.Zone w.toNat) → mid.memory w = s.memory w) ∧
        ∀ q ∈ ps, q.Done P0 mid := by
  intro ps
  induction ps with
  | nil =>
    intro F s post rest v _ _ _ _ _ _ _ run
    exact ⟨s,run,rfl,rfl,rfl,rfl,heapRel_preorder.refl _,by simp,fun _ _ _ _ _ => rfl,by simp⟩
  | cons q qs ih =>
    intro F s post rest v code hB hT ⟨p,hp,pP0,pal,pin⟩ ready apart budget run
    simp only [List.map_cons,unionChain,List.sum_cons] at run budget
    rw [evaluateHOLFiniteState_seq_line780] at run
    obtain ⟨⟨⟨dB,cB⟩,⟨dT,cT⟩,laid,tables,room,sinv,stables,arena⟩,footBelow,srcOwn,small⟩ := ready q List.mem_cons_self
    obtain ⟨apartHead,apartTail⟩ := List.pairwise_cons.mp apart
    cases callRun : evaluateHOLFiniteState s (mergeUnionCall q.o) with
    | mk r s1 =>
      rw [callRun] at run
      cases r with
      | some r =>
        exfalso
        obtain ⟨e,_⟩ := Prod.mk.inj run
        simp only [Option.some.injEq] at e
        subst e
        have := discard_call_not_returned s (ofString "htab_union_into")
          [.load .one (.op .add [.var .global (ofString "bs"),.const q.o]),
            .load .one (.op .add [.var .global (ofString "ts"),.const q.o])] v
        unfold mergeUnionCall at callRun
        rw [callRun] at this
        exact this rfl
      | none =>
        simp only at run
        have args := union_record_args s .global .global (ofString "bs") (ofString "ts") B T q.o q.o q.dst q.src
          (eval_global_word s _ B hB) (eval_global_word s _ T hT) dB cB dT cT
        have hdr : q.dst.toNat + 72 ≤ P0.toNat := by
          have := footBelow (q.dst.toNat + 71) (Or.inl (Or.inl ⟨by omega,by omega⟩)); omega
        unfold mergeUnionCall at callRun
        obtain ⟨D,⟨⟨p1,hp1,pp1,pal1,pin1⟩,rel1⟩,L,A,Be,C,Fr,Clk⟩ := htabUnionInto_tables_callT s s1 _ _ q.keyLength q.dst
          q.keys q.stride q.capacity q.used q.values q.order q.orderPos q.count q.bits q.lo q.hi laid tables room q.src q.skl
          q.skeys q.sstride q.scap q.sused q.svalues q.sorder q.sorderPos q.n q.sbits sinv stables args p hp pal pin
          (by omega) arena small
          (fun w h => by
            have b := footBelow w.toNat (Or.inr (Or.inr (Or.inl h)))
            have z := q.not_zone _ (srcOwn w.toNat h)
            exact ⟨by omega,z.1,z.2⟩)
          (by rw [UnionPair.cost_eq]; omega) callRun
        rw [UnionPair.cost_eq] at Clk
        -- what the call keeps
        have kept : ∀ w : BitVec 64, w.toNat < p.toNat → ¬ q.Zone w.toNat → s1.memory w = s.memory w := by
          intro w wlt nz
          have z := q.not_zone _ nz
          exact Fr w ⟨wlt,z.1,z.2⟩
        have readyTail : ∀ k ∈ qs, k.Ready B T s1 ∧ k.Placed B T P0 := by
          intro k mem
          obtain ⟨kr,kp⟩ := ready k (List.mem_cons_of_mem _ mem)
          refine ⟨k.ready_keep B T kr A Be C (fun w h => kept w ?_ ((apartHead k mem).2 _ h)),kp⟩
          have := kp.1 _ h; omega
        have glob : ∀ name, name ≠ ofString "heap_ptr" → s1.globals.lookup name = s.globals.lookup name :=
          rel1.1
        obtain ⟨mid,midRun,mc,ma,mb,ml,mrel,mclk,mframe,mdone⟩ := ih s1 post rest v (C.trans code)
          (by rw [glob _ (by decide)]; exact hB) (by rw [glob _ (by decide)]; exact hT)
          ⟨p1,hp1,by change p.toNat ≤ p1.toNat at pp1; omega,pal1,pin1⟩ readyTail apartTail (by omega) run
        refine ⟨mid,midRun,mc.trans C,ma.trans A,mb.trans Be,ml.trans L,heapRel_preorder.trans _ _ _ rel1 mrel,
          by simp only [List.map_cons,List.sum_cons]; omega,?_,?_⟩
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

#print axioms unionChain_returned

/-- The `merge_tx_into_block` body after its five union calls (the storage-table loop and return). -/
noncomputable def mergeTail : ProgHOL 64 := Classical.choose source_merge_unions

theorem source_merge_body : sourceFunctionBody Guest.guestFn_merge_tx_into_block =
    unionChain [24,8,40,16,48] mergeTail := Classical.choose_spec source_merge_unions

/-- The five `htab_union_into(lds(bs+o), lds(ts+o))` calls at the start of `merge_tx_into_block`
(o = 24, 8, 40, 16, 48), from five ready, placed, pairwise apart table pairs. -/
theorem merge_unions_returned (B T P0 : BitVec 64) (ps : List UnionPair) (offsets : ps.map UnionPair.o = [24,8,40,16,48])
    {F : Type} (s post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (code : s.code = originalRuntimeCode)
    (hB : s.globals.lookup (ofString "bs") = some (.val (.word B)))
    (hT : s.globals.lookup (ofString "ts") = some (.val (.word T)))
    (heap : ∃ p : BitVec 64, s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) ∧ P0.toNat ≤ p.toNat ∧
      p.toNat % 8 = 0 ∧ p.toNat ≤ 33806089496)
    (ready : ∀ q ∈ ps, q.Ready B T s ∧ q.Placed B T P0) (apart : ps.Pairwise (UnionPair.Apart B T))
    (budget : (ps.map UnionPair.cost).sum ≤ s.clock)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_merge_tx_into_block) = (some (.returned v),post)) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState mid mergeTail = (some (.returned v),post) ∧
      mid.code = s.code ∧ mid.memaddrs = s.memaddrs ∧ mid.be = s.be ∧ mid.locals = s.locals ∧
      HeapRel s.globals mid.globals ∧ s.clock ≤ mid.clock + (ps.map UnionPair.cost).sum ∧
      (∀ p : BitVec 64, s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) → ∀ w : BitVec 64,
        w.toNat < p.toNat → (∀ q ∈ ps, ¬ q.Zone w.toNat) → mid.memory w = s.memory w) ∧
      ∀ q ∈ ps, q.Done P0 mid := by
  rw [source_merge_body,← offsets] at run
  exact unionChain_returned B T P0 ps s post mergeTail v code hB hT heap ready apart budget run

#print axioms merge_unions_returned

/-- `incorporate_child_on_success`: the call `htab_union_into(lds(ev + 136), lds(child + 136))` with the
global `ev` and the local `child`, from table invariants. -/
theorem incorporate_union_call {F : Type} (state post : PanSemStateFiniteExact 64 F) (E C : BitVec 64)
    (hE : state.globals.lookup (ofString "ev") = some (.val (.word E)))
    (hC : state.locals.lookup (ofString "child") = some (.val (.word C)))
    (keyLength dst keys stride capacity used values order orderPos count : BitVec 64) (bits lo hi : Nat)
    (dD : state.memaddrs (E + 136)) (cD : state.memory (E + 136) = .word dst)
    (laid : HtabLaid keyLength dst keys stride capacity used values order orderPos count bits lo hi state)
    (tables : OrderInv state capacity count used order orderPos) (room : count.toNat < capacity.toNat)
    (src sKeyLength skeys sstride scapacity sused svalues sorder sorderPos n : BitVec 64) (sbits : Nat)
    (dS : state.memaddrs (C + 136)) (cS : state.memory (C + 136) = .word src)
    (sinv : HtabRegions sKeyLength src skeys sstride scapacity sused svalues sorder sorderPos n sbits state)
    (stables : OrderInv state scapacity n sused sorder sorderPos)
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
      lo hi state).stepCost + 1) + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_union_into")
      [.load .one (.op .add [.var .global (ofString "ev"),.const 136]),
        .load .one (.op .add [.var .local (ofString "child"),.const 136])]) = (none,post)) :
    (unionCtxOf keyLength dst stride src n skeys sstride svalues sorder count capacity pointer lo hi state).DstT n post ∧
      (unionCtxOf keyLength dst stride src n skeys sstride svalues sorder count capacity pointer lo hi state).Heap post ∧
      post.locals = state.locals ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ post.code = state.code ∧
      (∀ w, (unionCtxOf keyLength dst stride src n skeys sstride svalues sorder count capacity pointer lo hi state).Away w →
        post.memory w = state.memory w) ∧
      state.clock ≤ post.clock + (n.toNat * ((unionCtxOf keyLength dst stride src n skeys sstride svalues sorder count
        capacity pointer lo hi state).stepCost + 1) + 1) :=
  htabUnionInto_tables_callT state post _ _ keyLength dst keys stride capacity used values order orderPos count bits lo hi
    laid tables room src sKeyLength skeys sstride scapacity sused svalues sorder sorderPos n sbits sinv stables
    (union_record_args state .global .local (ofString "ev") (ofString "child") E C 136 136 dst src
      (eval_global_word state _ E hE) (item_eval_locals state _ C hC) dD cD dS cS)
    pointer heap pointerAligned pointerInside headerBelow arena small srcAway budget run

#print axioms incorporate_union_call
end InitECandidate.Runtime
