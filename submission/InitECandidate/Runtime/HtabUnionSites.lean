import InitECandidate.Runtime.HtabUnionInto
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-! Discharging the union source-read hypotheses from table invariants, footprint congruence of
the table invariants (they survive any change outside header/used/order/order_pos), and the
record-argument evaluation of the two `htab_union_into` call sites. -/

/-- Every memory cell holds a word (`HolWordLab` has no other constructor). -/
theorem memory_cell_word {F : Type} (s : PanSemStateFiniteExact 64 F) (a : BitVec 64) :
    ∃ w : BitVec 64, s.memory a = .word w := by
  cases h : s.memory a with
  | word w => exact ⟨w,rfl⟩

theorem HtabRegions.count_le {F : Type} {s : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat}
    (inv : HtabRegions keyLength table keys stride capacity used values order orderPos count bits s) :
    count.toNat ≤ capacity.toNat := by
  rw [inv.agreement]; unfold hashOccupiedCount; exact (List.countP_le_length).trans (by simp)

/-- The source reads of a union run hold for any source table (either layout, as a region table with
its order invariant) whose header, order array and value array lie away from the destination. -/
theorem UnionCtx.srcReads_of_table (c : UnionCtx) {F : Type} (s : PanSemStateFiniteExact 64 F)
    (memory0 : c.M0 = s.memory) (memaddrs0 : c.A0 = s.memaddrs)
    (keyLength capacity used orderPos : BitVec 64) (bits : Nat)
    (inv : HtabRegions keyLength c.src c.skeys c.sstride capacity used c.svalues c.sorder orderPos c.n bits s)
    (tables : OrderInv s capacity c.n used c.sorder orderPos)
    (away : ∀ w : BitVec 64, ((c.src.toNat ≤ w.toNat ∧ w.toNat < c.src.toNat + 72) ∨
      (c.sorder.toNat ≤ w.toNat ∧ w.toNat < c.sorder.toNat + capacity.toNat * 8) ∨
      (c.svalues.toNat ≤ w.toNat ∧ w.toNat < c.svalues.toNat + capacity.toNat * 8)) → c.Away w) :
    c.SrcReads := by
  have te := inv.tableEnd
  have hdr : ∀ k : Nat, k ≤ 64 → k % 8 = 0 →
      c.A0 (c.src + BitVec.ofNat 64 k) ∧ c.Away (c.src + BitVec.ofNat 64 k) := by
    intro k hk ha
    have eq := word_add_toNat c.src k (by omega)
    exact ⟨by rw [memaddrs0]; exact inv.header_domain k hk ha,away _ (Or.inl (by rw [eq]; omega))⟩
  have countLe := inv.count_le
  refine ⟨⟨(hdr 56 (by omega) (by omega)).1,by rw [memory0]; exact inv.cell56,(hdr 56 (by omega) (by omega)).2⟩,
    ⟨(hdr 32 (by omega) (by omega)).1,by rw [memory0]; exact inv.cell32,(hdr 32 (by omega) (by omega)).2⟩,
    ⟨(hdr 8 (by omega) (by omega)).1,by rw [memory0]; exact inv.cell8,(hdr 8 (by omega) (by omega)).2⟩,
    ⟨(hdr 40 (by omega) (by omega)).1,by rw [memory0]; exact inv.cell40,(hdr 40 (by omega) (by omega)).2⟩,?_⟩
  intro k lt
  obtain ⟨slot,cell,slotLt⟩ := tables.2 k lt
  obtain ⟨vv,vcell⟩ := memory_cell_word s (c.svalues + slot * 8)
  have kAt := (inv.slot_toNat k (by omega)).2.1
  have sAt := (inv.slot_toNat slot slotLt).1
  have oa := inv.orderAligned
  have va := inv.valuesAligned
  refine ⟨slot,vv,?_,by rw [memory0]; exact cell,away _ (Or.inr (Or.inl (by rw [kAt]; omega))),?_,
    by rw [memory0]; exact vcell,away _ (Or.inr (Or.inr (by rw [sAt]; omega)))⟩
  · rw [memaddrs0]; exact inv.order_domain _ (by rw [kAt]; omega) (by rw [kAt]; omega) (by rw [kAt]; omega)
  · rw [memaddrs0]; exact inv.values_domain _ (by rw [sAt]; omega) (by rw [sAt]; omega) (by rw [sAt]; omega)

#print axioms UnionCtx.srcReads_of_table

/-- Words a table invariant reads: header, occupancy array, order and order_pos arrays. -/
def HtabFoot (table capacity used order orderPos : BitVec 64) (w : Nat) : Prop :=
  (table.toNat ≤ w ∧ w < table.toNat + 72) ∨ (used.toNat ≤ w ∧ w < used.toNat + capacity.toNat) ∨
    (order.toNat ≤ w ∧ w < order.toNat + capacity.toNat * 8) ∨
    (orderPos.toNat ≤ w ∧ w < orderPos.toNat + capacity.toNat * 8)

/-- Agreement on the footprint, in the address forms the invariants read. -/
theorem HtabRegions.foot_keep {F G : Type} {s : PanSemStateFiniteExact 64 F} {r : PanSemStateFiniteExact 64 G}
    {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat}
    (inv : HtabRegions keyLength table keys stride capacity used values order orderPos count bits s)
    (keep : ∀ w : BitVec 64, HtabFoot table capacity used order orderPos w.toNat → r.memory w = s.memory w) :
    (∀ k : Nat, k ≤ 64 → r.memory (table + BitVec.ofNat 64 k) = s.memory (table + BitVec.ofNat 64 k)) ∧
    (∀ q : BitVec 64, q.toNat < capacity.toNat →
      r.memory (panByteAlignHOL (used + q)) = s.memory (panByteAlignHOL (used + q))) ∧
    (∀ q : BitVec 64, q.toNat < capacity.toNat → r.memory (order + q * 8) = s.memory (order + q * 8)) ∧
    (∀ q : BitVec 64, q.toNat < capacity.toNat → r.memory (orderPos + q * 8) = s.memory (orderPos + q * 8)) := by
  have te := inv.tableEnd; have ue := inv.usedEnd; have ua := inv.usedAligned
  refine ⟨fun k hk => keep _ (Or.inl (by rw [word_add_toNat table k (by omega)]; omega)),fun q lt => keep _ ?_,
    fun q lt => keep _ (Or.inr (Or.inr (Or.inl (by rw [(inv.slot_toNat q lt).2.1]; omega)))),
    fun q lt => keep _ (Or.inr (Or.inr (Or.inr (by rw [(inv.slot_toNat q lt).2.2.1]; omega))))⟩
  rw [byteAlign_toNat,BitVec.toNat_add_of_lt (by omega)]
  refine Or.inr (Or.inl ⟨?_,?_⟩)
  · have : used.toNat ≤ (used.toNat + q.toNat) / 8 * 8 := by
      have := Nat.div_mul_le_self (used.toNat + q.toNat) 8; omega
    exact this
  · have := Nat.div_mul_le_self (used.toNat + q.toNat) 8; omega

theorem HtabAligned.congr {F G : Type} {s : PanSemStateFiniteExact 64 F} {r : PanSemStateFiniteExact 64 G}
    {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat}
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits s)
    (memaddrs : r.memaddrs = s.memaddrs) (be : r.be = s.be) (code : r.code = s.code)
    (hdrK : ∀ k : Nat, k ≤ 64 → r.memory (table + BitVec.ofNat 64 k) = s.memory (table + BitVec.ofNat 64 k))
    (usedK : ∀ q : BitVec 64, q.toNat < capacity.toNat →
      r.memory (panByteAlignHOL (used + q)) = s.memory (panByteAlignHOL (used + q))) :
    HtabAligned keyLength table keys stride capacity used values order orderPos count bits r :=
  { inv with
    code := code.trans inv.code,
    domain := fun a h1 h2 h3 => by rw [memaddrs]; exact inv.domain a h1 h2 h3,
    cell0 := (hdrK 0 (by omega)).trans inv.cell0, cell8 := (hdrK 8 (by omega)).trans inv.cell8,
    cell16 := (hdrK 16 (by omega)).trans inv.cell16, cell24 := (hdrK 24 (by omega)).trans inv.cell24,
    cell32 := (hdrK 32 (by omega)).trans inv.cell32, cell40 := (hdrK 40 (by omega)).trans inv.cell40,
    cell48 := (hdrK 48 (by omega)).trans inv.cell48, cell56 := (hdrK 56 (by omega)).trans inv.cell56,
    cell64 := (hdrK 64 (by omega)).trans inv.cell64,
    agreement := by
      rw [inv.agreement]
      exact hashOccupiedCount_congr _ _ _ (fun q lt =>
        (occupancyRead_congr_at r s used q (usedK q lt) memaddrs be).symm) }

theorem HtabDescending.congr {F G : Type} {s : PanSemStateFiniteExact 64 F} {r : PanSemStateFiniteExact 64 G}
    {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat}
    (inv : HtabDescending keyLength table keys stride capacity used values order orderPos count bits s)
    (memaddrs : r.memaddrs = s.memaddrs) (be : r.be = s.be) (code : r.code = s.code)
    (hdrK : ∀ k : Nat, k ≤ 64 → r.memory (table + BitVec.ofNat 64 k) = s.memory (table + BitVec.ofNat 64 k))
    (usedK : ∀ q : BitVec 64, q.toNat < capacity.toNat →
      r.memory (panByteAlignHOL (used + q)) = s.memory (panByteAlignHOL (used + q))) :
    HtabDescending keyLength table keys stride capacity used values order orderPos count bits r :=
  { inv with
    code := code.trans inv.code,
    domain := fun a h1 h2 h3 => by rw [memaddrs]; exact inv.domain a h1 h2 h3,
    cell0 := (hdrK 0 (by omega)).trans inv.cell0, cell8 := (hdrK 8 (by omega)).trans inv.cell8,
    cell16 := (hdrK 16 (by omega)).trans inv.cell16, cell24 := (hdrK 24 (by omega)).trans inv.cell24,
    cell32 := (hdrK 32 (by omega)).trans inv.cell32, cell40 := (hdrK 40 (by omega)).trans inv.cell40,
    cell48 := (hdrK 48 (by omega)).trans inv.cell48, cell56 := (hdrK 56 (by omega)).trans inv.cell56,
    cell64 := (hdrK 64 (by omega)).trans inv.cell64,
    agreement := by
      rw [inv.agreement]
      exact hashOccupiedCount_congr _ _ _ (fun q lt =>
        (occupancyRead_congr_at r s used q (usedK q lt) memaddrs be).symm) }

theorem HtabRegions.congr {F G : Type} {s : PanSemStateFiniteExact 64 F} {r : PanSemStateFiniteExact 64 G}
    {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat}
    (inv : HtabRegions keyLength table keys stride capacity used values order orderPos count bits s)
    (memaddrs : r.memaddrs = s.memaddrs) (be : r.be = s.be) (code : r.code = s.code)
    (keep : ∀ w : BitVec 64, HtabFoot table capacity used order orderPos w.toNat → r.memory w = s.memory w) :
    HtabRegions keyLength table keys stride capacity used values order orderPos count bits r :=
  have K := inv.foot_keep keep
  { inv with
    code := code.trans inv.code,
    domain := fun a h1 h2 => by rw [memaddrs]; exact inv.domain a h1 h2,
    cell0 := (K.1 0 (by omega)).trans inv.cell0, cell8 := (K.1 8 (by omega)).trans inv.cell8,
    cell16 := (K.1 16 (by omega)).trans inv.cell16, cell24 := (K.1 24 (by omega)).trans inv.cell24,
    cell32 := (K.1 32 (by omega)).trans inv.cell32, cell40 := (K.1 40 (by omega)).trans inv.cell40,
    cell48 := (K.1 48 (by omega)).trans inv.cell48, cell56 := (K.1 56 (by omega)).trans inv.cell56,
    cell64 := (K.1 64 (by omega)).trans inv.cell64,
    agreement := by
      rw [inv.agreement]
      exact hashOccupiedCount_congr _ _ _ (fun q lt =>
        (occupancyRead_congr_at r s used q (K.2.1 q lt) memaddrs be).symm) }

theorem OrderInv.congr {F G : Type} {s : PanSemStateFiniteExact 64 F} {r : PanSemStateFiniteExact 64 G}
    {capacity count used order orderPos : BitVec 64}
    (o : OrderInv s capacity count used order orderPos) (countLe : count.toNat ≤ capacity.toNat)
    (memaddrs : r.memaddrs = s.memaddrs) (be : r.be = s.be)
    (usedK : ∀ q : BitVec 64, q.toNat < capacity.toNat →
      r.memory (panByteAlignHOL (used + q)) = s.memory (panByteAlignHOL (used + q)))
    (orderK : ∀ q : BitVec 64, q.toNat < capacity.toNat → r.memory (order + q * 8) = s.memory (order + q * 8))
    (posK : ∀ q : BitVec 64, q.toNat < capacity.toNat → r.memory (orderPos + q * 8) = s.memory (orderPos + q * 8)) :
    OrderInv r capacity count used order orderPos := by
  constructor
  · intro q inside occupied
    have read := occupancyRead_congr_at r s used q (usedK q inside) memaddrs be
    obtain ⟨y,hy,ylt⟩ := o.1 q inside (by rw [← read]; exact occupied)
    exact ⟨y,by rw [posK q inside]; exact hy,ylt⟩
  · intro k inside
    obtain ⟨x,hx,xlt⟩ := o.2 k inside
    exact ⟨x,by rw [orderK k (by omega)]; exact hx,xlt⟩

/-- A laid-out table with its order invariant survives any change outside its footprint. -/
theorem HtabLaid.congr_tables {F G : Type} {s : PanSemStateFiniteExact 64 F} {r : PanSemStateFiniteExact 64 G}
    {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat} {lo hi : Nat}
    (laid : HtabLaid keyLength table keys stride capacity used values order orderPos count bits lo hi s)
    (o : OrderInv s capacity count used order orderPos)
    (memaddrs : r.memaddrs = s.memaddrs) (be : r.be = s.be) (code : r.code = s.code)
    (keep : ∀ w : BitVec 64, HtabFoot table capacity used order orderPos w.toNat → r.memory w = s.memory w) :
    HtabLaid keyLength table keys stride capacity used values order orderPos count bits lo hi r ∧
      OrderInv r capacity count used order orderPos := by
  have K := laid.regions.foot_keep keep
  refine ⟨?_,o.congr laid.regions.count_le memaddrs be K.2.1 K.2.2.1 K.2.2.2⟩
  rcases laid with ⟨inv,l,h⟩ | ⟨inv,l,h⟩
  · exact Or.inl ⟨inv.congr memaddrs be code K.1 K.2.1,l,h⟩
  · exact Or.inr ⟨inv.congr memaddrs be code K.1 K.2.1,l,h⟩

#print axioms HtabRegions.congr
#print axioms HtabLaid.congr_tables

/-- The union run context of a call from `state`. -/
def unionCtxOf {F : Type} (keyLength dst stride src n skeys sstride svalues sorder count0 capacity0 pointer0 : BitVec 64)
    (lo0 hi0 : Nat) (state : PanSemStateFiniteExact 64 F) : UnionCtx :=
  ⟨keyLength,dst,stride,src,n,skeys,sstride,svalues,sorder,count0,capacity0,pointer0,lo0,hi0,
    state.memory,state.memaddrs,state.globals⟩

/-- The discarded `htab_union_into(dst, src)` call from table invariants: the destination is laid out
(aligned or descending) with room, the source is any region table with its order invariant, and the
source header, order array and value array lie below the heap pointer outside the destination's header
and array block. -/
theorem htabUnionInto_tables_call_normal {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (unionCtxOf keyLength dst stride src n skeys sstride svalues sorder count capacity pointer lo hi state).Dst n post ∧
      (unionCtxOf keyLength dst stride src n skeys sstride svalues sorder count capacity pointer lo hi state).Heap post ∧
      post.locals = state.locals ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ post.code = state.code ∧
      ∀ w, (unionCtxOf keyLength dst stride src n skeys sstride svalues sorder count capacity pointer lo hi state).Away w →
        post.memory w = state.memory w := by
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
  exact htabUnionInto_call_normal _ ok reads state post dstArgument srcArgument laid.code args
    (sinv.header_domain 24 (by omega) (by omega)) sinv.cell24 rfl rfl rfl
    ⟨keys,used,values,order,orderPos,bits,laid,tables⟩ heap budget run

#print axioms htabUnionInto_tables_call_normal

/-- A record word `lds 1 (base + offset)` with the base in a variable. -/
theorem eval_record_word {F : Type} (s : PanSemStateFiniteExact 64 F) (kind : VarKind) (name : MlS)
    (base offset value : BitVec 64)
    (binding : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.var kind name) =
      some (.val (.word base)))
    (domain : s.memaddrs (base + offset)) (cell : s.memory (base + offset) = .word value) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var kind name,.const offset])) = some (.val (.word value)) :=
  eval_load_word s _ _ value (eval_add2 s _ _ base offset binding (item_eval_const s offset)) domain cell

theorem eval_global_word {F : Type} (s : PanSemStateFiniteExact 64 F) (name : MlS) (w : BitVec 64)
    (h : s.globals.lookup name = some (.val (.word w))) :
    @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) (.var .global name) =
      some (.val (.word w)) := by
  simpa [evalHOLExact] using h

/-- Both union call sites pass two record words: `merge_tx_into_block` reads `bs + o` and `ts + o`
(globals), `incorporate_child_on_success` reads `ev + 136` (global) and `child + 136` (local). -/
theorem union_record_args {F : Type} (s : PanSemStateFiniteExact 64 F) (k1 k2 : VarKind) (n1 n2 : MlS)
    (b1 b2 o1 o2 dst src : BitVec 64)
    (h1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.var k1 n1) =
      some (.val (.word b1)))
    (h2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.var k2 n2) =
      some (.val (.word b2)))
    (d1 : s.memaddrs (b1 + o1)) (c1 : s.memory (b1 + o1) = .word dst)
    (d2 : s.memaddrs (b2 + o2)) (c2 : s.memory (b2 + o2) = .word src) :
    evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.load .one (.op .add [.var k1 n1,.const o1]),.load .one (.op .add [.var k2 n2,.const o2])] =
      some [.val (.word dst),.val (.word src)] := by
  rw [evalListHOLFinite_eq_toExact]
  simp only [evalListHOLExact,eval_record_word s k1 n1 b1 o1 dst h1 d1 c1,eval_record_word s k2 n2 b2 o2 src h2 d2 c2]

#print axioms union_record_args
end InitECandidate.Runtime
