import InitECandidate.Runtime.HtabNewTop
import InitECandidate.Runtime.HtabUnionMerge
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-! The `merge_tx_into_block` storage loop (`mergeTail`): its program pieces, the loop invariant
(`MergeCtx.CoreW`: block map `bouter` with values in a registry of inner tables, registered inner tables
with pairwise apart zones, outer footprint unchanged, heap monotone) and its preservation by each call of
an iteration (`htab_new`, `htab_set` on the block map, nested `htab_union_into` on an inner table). -/

/-- A table zone: the header and the array block. -/
def TZone (t : BitVec 64) (lo hi : Nat) (w : Nat) : Prop :=
  (t.toNat ≤ w ∧ w < t.toNat + 72) ∨ (lo ≤ w ∧ w < hi)

/-- An inner (per-account) table of the block storage map in state s: laid out, order invariant, room,
block ending at or below `top`, header at or above `L`, with size bounds. -/
def InnerTab (KI : BitVec 64) (L top : Nat) (NI CI : Nat) {F : Type} (s : PanSemStateFiniteExact 64 F)
    (b : BitVec 64) (lo hi : Nat) : Prop :=
  ∃ (capacity keys stride used values order orderPos count : BitVec 64) (bits : Nat),
    HtabLaid KI b keys stride capacity used values order orderPos count bits lo hi s ∧
    OrderInv s capacity count used order orderPos ∧ count.toNat < capacity.toNat ∧
    hi ≤ top ∧ L ≤ b.toNat ∧ count.toNat ≤ NI ∧ capacity.toNat ≤ CI

theorem InnerTab.congr {KI : BitVec 64} {L top NI CI : Nat} {F : Type} {s r : PanSemStateFiniteExact 64 F}
    {b : BitVec 64} {lo hi : Nat} (t : InnerTab KI L top NI CI s b lo hi)
    (memaddrs : r.memaddrs = s.memaddrs) (be : r.be = s.be) (code : r.code = s.code)
    (keep : ∀ w : BitVec 64, TZone b lo hi w.toNat → r.memory w = s.memory w)
    {top' : Nat} (le : top ≤ top') : InnerTab KI L top' NI CI r b lo hi := by
  obtain ⟨c,k,st,u,v,o,op,n,bits,laid,tables,room,h1,h2,h3,h4⟩ := t
  obtain ⟨laid',tables'⟩ := laid.congr_tables tables memaddrs be code (fun w h => keep w (laid.foot_sub w.toNat h))
  exact ⟨c,k,st,u,v,o,op,n,bits,laid',tables',room,by omega,h2,h3,h4⟩

#print axioms InnerTab.congr

def mergeNewSet : ProgHOL 64 :=
  .seq (.call (some (some (.local,ofString "binner"),none)) (ofString "htab_new") [.const 32,.const 8])
    (.call (some (none,none)) (ofString "htab_set")
      [.var .local (ofString "bouter"),.rfield 1 (.var .local (ofString "s")),.var .local (ofString "binner")])

def mergeChoose : ProgHOL 64 :=
  .ite (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0)) mergeNewSet
    (.assign .local (ofString "binner") (.rfield 1 (.var .local (ofString "m"))))

def mergeUnionInner : ProgHOL 64 :=
  .call (some (none,none)) (ofString "htab_union_into")
    [.var .local (ofString "binner"),.rfield 2 (.var .local (ofString "s"))]

def mergeInner : ProgHOL 64 :=
  .decCall (ofString "m") (.comb [.one,.one]) (ofString "htab_get")
    [.var .local (ofString "bouter"),.rfield 1 (.var .local (ofString "s"))]
    (.dec (ofString "binner") .one (.const 0) (.seq mergeChoose mergeUnionInner))

def mergeIter : ProgHOL 64 :=
  .decCall (ofString "s") (.comb [.one,.one,.one]) (ofString "htab_item")
    [.var .local (ofString "outer"),.var .local (ofString "i")]
    (.seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s"))) (.const 0)) mergeInner .skip)
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])))

def mergeCond : ExpHOL 64 := .cmp .less (.var .local (ofString "i")) (.var .local (ofString "cap"))

def mergeTailE : ProgHOL 64 :=
  .dec (ofString "outer") .one (.load .one (.op .add [.var .global (ofString "ts"),.const 32]))
    (.dec (ofString "bouter") .one (.load .one (.op .add [.var .global (ofString "bs"),.const 32]))
      (.dec (ofString "cap") .one (.load .one (.op .add [.var .local (ofString "outer"),.const 24]))
        (.dec (ofString "i") .one (.const 0)
          (.seq (.while mergeCond mergeIter) (.return (.const 0))))))

theorem source_merge_body_explicit : sourceFunctionBody Guest.guestFn_merge_tx_into_block =
    unionChain [24,8,40,16,48] mergeTailE := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem mergeTail_eq : mergeTail = mergeTailE := by
  have h := source_merge_body.symm.trans source_merge_body_explicit
  simp only [unionChain,ProgHOL.seq.injEq] at h
  exact h.2.2.2.2.2

#print axioms mergeTail_eq

/-- Fixed data of one storage-loop run: the outer (transaction) map with its header words, the block map
`bouter` with key length/stride, the inner tables' key length/stride, the entry heap pointer, the arena
start, size bounds, the entry memory/addresses/endianness/globals, and the outer-side footprint. -/
structure MergeCtx where
  O : BitVec 64
  n : BitVec 64
  okeys : BitVec 64
  ostride : BitVec 64
  ovals : BitVec 64
  oorder : BitVec 64
  BO : BitVec 64
  KB : BitVec 64
  SB : BitVec 64
  KI : BitVec 64
  SI : BitVec 64
  P0 : BitVec 64
  L : Nat
  NB0 : Nat
  CB : Nat
  NI0 : Nat
  CI : Nat
  NS : Nat
  M0 : BitVec 64 → HolWordLab 64
  A0 : BitVec 64 → Prop
  BE : Bool
  G0 : HolFiniteMapExact MlS (ValueHOL 64)
  OFoot : Nat → Prop

/-- The block map: aligned, order invariant, room, values in the registry, below the heap pointer, sized,
and its zone avoiding the outer footprint and every registered inner zone. -/
def MergeCtx.Bouter (c : MergeCtx) (I : Nat) {F : Type} (s : PanSemStateFiniteExact 64 F) (top : Nat)
    (R : Set (BitVec 64)) (Z : BitVec 64 → Nat × Nat) : Prop :=
  ∃ (bcap bkeys bused bvals border bop bcount : BitVec 64) (bbits : Nat),
    HtabAligned c.KB c.BO bkeys c.SB bcap bused bvals border bop bcount bbits s ∧
    OrderInv s bcap bcount bused border bop ∧ bcount.toNat < bcap.toNat ∧
    VTabs R s bcap bcount bused bkeys c.SB bvals border ∧ bop.toNat + bcap.toNat * 8 ≤ top ∧
    bcount.toNat ≤ c.NB0 + I ∧ bcap.toNat ≤ c.CB ∧
    ∀ w, TZone c.BO (min bkeys.toNat bvals.toNat) (bop.toNat + bcap.toNat * 8) w →
      ¬ c.OFoot w ∧ ∀ b ∈ R, ¬ TZone b (Z b).1 (Z b).2 w

/-- The registered inner tables: valid, avoiding the outer footprint, pairwise apart. -/
def MergeCtx.Inners (c : MergeCtx) (I : Nat) {F : Type} (s : PanSemStateFiniteExact 64 F) (top : Nat)
    (R : Set (BitVec 64)) (Z : BitVec 64 → Nat × Nat) : Prop :=
  (∀ b ∈ R, InnerTab c.KI c.L top (c.NI0 + I * c.NS) c.CI s b (Z b).1 (Z b).2) ∧
  (∀ b ∈ R, ∀ w, TZone b (Z b).1 (Z b).2 w → ¬ c.OFoot w) ∧
  (∀ b ∈ R, ∀ b' ∈ R, b ≠ b' → ∀ w, TZone b (Z b).1 (Z b).2 w → ¬ TZone b' (Z b').1 (Z b').2 w)

/-- Everything the loop keeps apart from its locals, with explicit heap pointer, registry and zones;
`IB` and `II` index the block-map and inner-table count bounds. -/
def MergeCtx.CoreW (c : MergeCtx) (IB II : Nat) {F : Type} (s : PanSemStateFiniteExact 64 F) (p : BitVec 64)
    (R : Set (BitVec 64)) (Z : BitVec 64 → Nat × Nat) : Prop :=
  s.code = originalRuntimeCode ∧ s.memaddrs = c.A0 ∧ s.be = c.BE ∧
  (∀ w : BitVec 64, c.OFoot w.toNat → s.memory w = c.M0 w) ∧
  s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) ∧ c.P0.toNat ≤ p.toNat ∧
  p.toNat % 8 = 0 ∧ p.toNat ≤ 33806089496 ∧ HeapRel c.G0 s.globals ∧
  c.Bouter IB s p.toNat R Z ∧ c.Inners II s p.toNat R Z

/-- Loop rank: the counter, the loop locals, and the core. -/
def MergeRank (c : MergeCtx) {F : Type} (s : PanSemStateFiniteExact 64 F) (m : Nat) : Prop :=
  ∃ I : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat ≤ c.n.toNat ∧
    c.n.toNat - I.toNat ≤ m ∧ s.locals.lookup (ofString "cap") = some (.val (.word c.n)) ∧
    s.locals.lookup (ofString "outer") = some (.val (.word c.O)) ∧
    s.locals.lookup (ofString "bouter") = some (.val (.word c.BO)) ∧
    ∃ p R Z, c.CoreW I.toNat I.toNat s p R Z

theorem VTabs.congr {F G : Type} {s : PanSemStateFiniteExact 64 F} {r : PanSemStateFiniteExact 64 G}
    {targets : Set (BitVec 64)} {keyLength table keys stride capacity used values order orderPos count : BitVec 64}
    {bits : Nat} (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits s)
    (tables : OrderInv s capacity count used order orderPos)
    (vt : VTabs targets s capacity count used keys stride values order)
    (memaddrs : r.memaddrs = s.memaddrs) (be : r.be = s.be)
    (keep : ∀ w : BitVec 64, (min keys.toNat values.toNat ≤ w.toNat ∧ w.toNat < orderPos.toNat + capacity.toNat * 8) →
      r.memory w = s.memory w) :
    VTabs targets r capacity count used keys stride values order := by
  have kb := inv.keysBefore; have vb := inv.valuesBefore; have ub := inv.usedBefore; have ob := inv.orderBefore
  have ua := inv.usedAligned
  have countLe := inv.toRegions.count_le
  have occ : ∀ q : BitVec 64, q.toNat < capacity.toNat → hashOccupancyRead r used q = hashOccupancyRead s used q := by
    intro q lt
    apply occupancyRead_congr_at r s used q _ memaddrs be
    apply keep
    rw [byteAlign_toNat,BitVec.toNat_add_of_lt (by have := inv.endBound; omega)]
    have := Nat.div_mul_le_self (used.toNat + q.toNat) 8
    have : used.toNat ≤ (used.toNat + q.toNat) / 8 * 8 := by
      have h := Nat.div_mul_le_self (used.toNat + q.toNat) 8
      omega
    have : min keys.toNat values.toNat ≤ keys.toNat := Nat.min_le_left _ _
    constructor <;> omega
  obtain ⟨a,b,cs⟩ := vt
  refine ⟨fun k lt slot cell => ?_,fun q lt o v cell => ?_,cs⟩
  · obtain ⟨x,hx,xlt⟩ := tables.2 k lt
    have kN := (inv.slot_toNat k (by omega)).2.1
    have mk : min keys.toNat values.toNat ≤ keys.toNat := Nat.min_le_left _ _
    rw [keep _ ⟨by rw [kN]; omega,by rw [kN]; omega⟩,hx] at cell
    simp only [HolWordLab.word.injEq] at cell
    subst cell
    rw [occ x xlt]
    exact a k lt x hx
  · have qN := (inv.slot_toNat q lt).1
    have mv : min keys.toNat values.toNat ≤ values.toNat := Nat.min_le_right _ _
    rw [keep _ ⟨by rw [qN]; omega,by rw [qN]; omega⟩] at cell
    exact b q lt (by rw [← occ q lt]; exact o) v cell

theorem VTabs.mono {F : Type} {s : PanSemStateFiniteExact 64 F} {targets targets' : Set (BitVec 64)}
    {capacity count used keys stride values order : BitVec 64}
    (vt : VTabs targets s capacity count used keys stride values order) (sub : targets ⊆ targets') :
    VTabs targets' s capacity count used keys stride values order :=
  ⟨vt.1,fun q lt o v cell => sub (vt.2.1 q lt o v cell),vt.2.2⟩

#print axioms VTabs.congr

theorem HtabLaid.header_le_hi {F : Type} {s : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat} {lo hi : Nat}
    (laid : HtabLaid keyLength table keys stride capacity used values order orderPos count bits lo hi s) :
    table.toNat + 72 ≤ hi ∧ lo ≤ hi := by
  rcases laid with ⟨inv,rfl,rfl⟩ | ⟨inv,rfl,rfl⟩
  · have := inv.headerKeys; have := inv.keysBefore; have := inv.usedBefore; have := inv.orderBefore
    have := inv.headerValues; have := inv.valuesBefore
    have : min keys.toNat values.toNat ≤ keys.toNat := Nat.min_le_left _ _
    have : keys.toNat ≤ keys.toNat + capacity.toNat * stride.toNat := Nat.le_add_right _ _
    constructor <;> omega
  · have := inv.keysBelow; have := inv.valuesBelow; have := inv.usedBelow; have := inv.orderBelow
    have := inv.orderPosBelow
    have : keys.toNat ≤ keys.toNat + capacity.toNat * stride.toNat := Nat.le_add_right _ _
    constructor <;> omega

theorem InnerTab.zone_below {KI : BitVec 64} {L top NI CI : Nat} {F : Type} {s : PanSemStateFiniteExact 64 F}
    {b : BitVec 64} {lo hi : Nat} (t : InnerTab KI L top NI CI s b lo hi) (w : Nat) (h : TZone b lo hi w) :
    w < top := by
  obtain ⟨_,_,_,_,_,_,_,_,_,laid,_,_,h1,_⟩ := t
  have := laid.header_le_hi
  unfold TZone at h
  omega

theorem InnerTab.mono {KI : BitVec 64} {L top NI CI NI' : Nat} {F : Type} {s : PanSemStateFiniteExact 64 F}
    {b : BitVec 64} {lo hi : Nat} (t : InnerTab KI L top NI CI s b lo hi) (le : NI ≤ NI') :
    InnerTab KI L top NI' CI s b lo hi := by
  obtain ⟨c,k,st,u,v,o,op,n,bits,laid,tables,room,h1,h2,h3,h4⟩ := t
  exact ⟨c,k,st,u,v,o,op,n,bits,laid,tables,room,h1,h2,by omega,h4⟩

theorem MergeCtx.CoreW.weaken {c : MergeCtx} {IB II IB' II' : Nat} {F : Type} {s : PanSemStateFiniteExact 64 F}
    {p : BitVec 64} {R : Set (BitVec 64)} {Z : BitVec 64 → Nat × Nat} (core : c.CoreW IB II s p R Z)
    (hb : IB ≤ IB') (hi : II ≤ II') : c.CoreW IB' II' s p R Z := by
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,⟨bc,bk,bu,bv,bo,bp,bn,bb,binv,bt,br,bvt,btop,bnb,bcb,bz⟩,⟨ii,io,ip⟩⟩ := core
  have : II * c.NS ≤ II' * c.NS := Nat.mul_le_mul_right _ hi
  exact ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,⟨bc,bk,bu,bv,bo,bp,bn,bb,binv,bt,br,bvt,btop,by omega,bcb,bz⟩,
    ⟨fun b mem => (ii b mem).mono (by omega),io,ip⟩⟩

theorem MergeCtx.CoreW.transfer {c : MergeCtx} {IB II : Nat} {F : Type} {s r : PanSemStateFiniteExact 64 F}
    {p : BitVec 64} {R : Set (BitVec 64)} {Z : BitVec 64 → Nat × Nat} (core : c.CoreW IB II s p R Z)
    (memory : r.memory = s.memory) (memaddrs : r.memaddrs = s.memaddrs) (be : r.be = s.be) (code : r.code = s.code)
    (globals : r.globals = s.globals) : c.CoreW IB II r p R Z := by
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,⟨bc,bk,bu,bv,bo,bp,bn,bb,binv,bt,br,bvt,btop,bnb,bcb,bz⟩,⟨ii,io,ip⟩⟩ := core
  exact ⟨code.trans a1,memaddrs.trans a2,be.trans a3,fun w h => by rw [memory]; exact a4 w h,by rw [globals]; exact a5,a6,
    a7,a8,by rw [globals]; exact a9,
    ⟨bc,bk,bu,bv,bo,bp,bn,bb,binv.transfer memory memaddrs be code,bt.transfer memory memaddrs be,br,
      bvt.transfer memory memaddrs be,btop,bnb,bcb,bz⟩,
    ⟨fun b mem => (ii b mem).congr memaddrs be code (fun w _ => by rw [memory]) (le_refl _),io,ip⟩⟩

#print axioms MergeCtx.CoreW.transfer

theorem HtabAligned.foot_below {F : Type} {s : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat}
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits s) (w : Nat)
    (h : HtabFoot table capacity used order orderPos w) : w < orderPos.toNat + capacity.toNat * 8 := by
  have := inv.headerKeys; have := inv.keysBefore; have := inv.usedBefore; have := inv.orderBefore
  have : keys.toNat ≤ keys.toNat + capacity.toNat * stride.toNat := Nat.le_add_right _ _
  unfold HtabFoot at h
  omega

/-- Below-`top` agreement transfers an aligned table with its order invariant. -/
theorem HtabAligned.keep_below {F G : Type} {s : PanSemStateFiniteExact 64 F} {r : PanSemStateFiniteExact 64 G}
    {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat}
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits s)
    (tables : OrderInv s capacity count used order orderPos)
    (memaddrs : r.memaddrs = s.memaddrs) (be : r.be = s.be) (code : r.code = s.code) (top : Nat)
    (below : orderPos.toNat + capacity.toNat * 8 ≤ top)
    (keep : ∀ w : BitVec 64, w.toNat < top → r.memory w = s.memory w) :
    HtabAligned keyLength table keys stride capacity used values order orderPos count bits r ∧
      OrderInv r capacity count used order orderPos := by
  have K := inv.toRegions.foot_keep (r := r) (fun w h => keep w (by have := inv.foot_below w.toNat h; omega))
  exact ⟨inv.congr memaddrs be code K.1 K.2.1,tables.congr inv.toRegions.count_le memaddrs be K.2.1 K.2.2.1 K.2.2.2⟩

theorem InnerTab.code {KI : BitVec 64} {L top NI CI : Nat} {F : Type} {s : PanSemStateFiniteExact 64 F}
    {b : BitVec 64} {lo hi : Nat} (t : InnerTab KI L top NI CI s b lo hi) : s.code = originalRuntimeCode := by
  obtain ⟨_,_,_,_,_,_,_,_,_,laid,_⟩ := t
  exact laid.code

/-- Static requirements of a storage-loop run. -/
structure MergeCtx.Static (c : MergeCtx) : Prop where
  kI : c.KI = 32
  LP : c.L ≤ c.P0.toNat
  LB : c.L ≤ c.BO.toNat
  ci8 : 8 ≤ c.CI
  ofBelow : ∀ w, c.OFoot w → w < c.P0.toNat
  arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → c.L ≤ a.toNat → a.toNat < 33806089496 → c.A0 a
  kbSmall : c.KB.toNat ≤ 33806089496
  ciSmall : c.CI ≤ 33806089496
  cbSmall : c.CB ≤ 33806089496

theorem MergeCtx.Bouter.zone_below {c : MergeCtx} {F : Type} {s : PanSemStateFiniteExact 64 F} {top : Nat}
    (bcap bkeys bused bvals border bop bcount : BitVec 64) (bbits : Nat)
    (inv : HtabAligned c.KB c.BO bkeys c.SB bcap bused bvals border bop bcount bbits s)
    (btop : bop.toNat + bcap.toNat * 8 ≤ top) (w : Nat)
    (h : TZone c.BO (min bkeys.toNat bvals.toNat) (bop.toNat + bcap.toNat * 8) w) : w < top := by
  have := (show HtabLaid c.KB c.BO bkeys c.SB bcap bused bvals border bop bcount bbits
    (min bkeys.toNat bvals.toNat) (bop.toNat + bcap.toNat * 8) s from Or.inl ⟨inv,rfl,rfl⟩).header_le_hi
  unfold TZone at h
  omega

set_option maxHeartbeats 2000000 in
/-- `binner = htab_new(32, 8)`: the fresh table at the old heap pointer joins the registry. -/
theorem MergeCtx.CoreW.after_new {c : MergeCtx} (st : c.Static) {IB II : Nat} {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (p : BitVec 64) (R : Set (BitVec 64)) (Z : BitVec 64 → Nat × Nat)
    (core : c.CoreW IB II s p R Z) (budget : 8 + 14 ≤ s.clock)
    (run : evaluateHOLFiniteState s (.call (some (some (.local,ofString "binner"),none)) (ofString "htab_new")
      [.const 32,.const 8]) = (none,post)) :
    ∃ (p' : BitVec 64) (Z' : BitVec 64 → Nat × Nat),
      post.locals.lookup (ofString "binner") = some (.val (.word p)) ∧
      (∀ k, k ≠ ofString "binner" → post.locals.lookup k = s.locals.lookup k) ∧
      c.CoreW IB II post p' (insert p R) Z' ∧ (∀ b ∈ R, Z' b = Z b) ∧ p ∉ R := by
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,⟨bc,bk,bu,bv,bo,bp,bn,bb,binv,bt,br,bvt,btop,bnb,bcb,bz⟩,⟨ii,io,ip⟩⟩ := core
  have LP := st.LP
  obtain ⟨keys,stride,used,values,order,orderPos,inv,tables,pa,pb,pl,po,frame,⟨p',hp',le',pal',pin'⟩,rel⟩ :=
    htabNew_call_assign s post (ofString "binner") 32 8 p 3 a1 a5 a7 a8
    (fun a h1 h2 h3 => by rw [a2]; exact st.arena a h1 (by omega) h3) rfl (by decide) budget run
  have hk := inv.headerKeys; have kb := inv.keysBefore; have ub := inv.usedBefore; have ob := inv.orderBefore
  have hv := inv.headerValues; have vb := inv.valuesBefore
  have zoneR : ∀ b ∈ R, ∀ w, TZone b (Z b).1 (Z b).2 w → w < p.toNat := fun b mem w h => (ii b mem).zone_below w h
  have notIn : p ∉ R := by
    intro mem
    have := zoneR p mem p.toNat (Or.inl ⟨le_refl _,by omega⟩)
    omega
  have ofB := st.ofBelow
  have bzB := MergeCtx.Bouter.zone_below bc bk bu bv bo bp bn bb binv btop
  have postCode : post.code = originalRuntimeCode := inv.code
  have keepBelow : ∀ w : BitVec 64, w.toNat < p.toNat → post.memory w = s.memory w := frame
  let Z' : BitVec 64 → Nat × Nat := fun b => if b = p then (min keys.toNat values.toNat, orderPos.toNat + (8 : BitVec 64).toNat * 8) else Z b
  have zR : ∀ b ∈ R, Z' b = Z b := by
    intro b mem
    have : b ≠ p := fun e => notIn (e ▸ mem)
    simp [Z',this]
  have zP : Z' p = (min keys.toNat values.toNat, orderPos.toNat + (8 : BitVec 64).toNat * 8) := by simp [Z']
  have newZone : ∀ w, TZone p (Z' p).1 (Z' p).2 w → p.toNat ≤ w := by
    intro w h; rw [zP] at h; unfold TZone at h
    have : p.toNat + 72 ≤ min keys.toNat values.toNat := Nat.le_min.mpr ⟨hk,hv⟩
    omega
  refine ⟨p',Z',pl,po,⟨postCode,pa.trans a2,pb.trans a3,fun w h => by
      rw [keepBelow w (by have := ofB _ h; omega)]; exact a4 w h,hp',by omega,pal',pin',
      heapRel_preorder.trans _ _ _ a9 rel,?_,?_⟩,zR,notIn⟩
  · -- the block map, below the old heap pointer, is untouched
    obtain ⟨binv',bt'⟩ := binv.keep_below bt pa pb (postCode.trans binv.code.symm) p.toNat btop keepBelow
    refine ⟨bc,bk,bu,bv,bo,bp,bn,bb,binv',bt',br,?_,by omega,bnb,bcb,?_⟩
    · exact (bvt.congr binv bt pa pb (fun w h => keepBelow w (by omega))).mono (Set.subset_insert _ _)
    · intro w h
      refine ⟨(bz w h).1,fun b mem => ?_⟩
      rcases Set.mem_insert_iff.mp mem with rfl | inR
      · have := bzB w h
        intro hz; have := newZone w hz; omega
      · rw [zR b inR]; exact (bz w h).2 b inR
  · refine ⟨fun b mem => ?_,fun b mem w h => ?_,fun b mb b' mb' ne w h h' => ?_⟩
    · rcases Set.mem_insert_iff.mp mem with rfl | inR
      · rw [zP]
        exact ⟨8,keys,stride,used,values,order,orderPos,0,3,Or.inl ⟨by rw [st.kI]; exact inv,rfl,rfl⟩,tables,by decide,
          le',by omega,by simp,st.ci8⟩
      · rw [zR b inR]
        exact (ii b inR).congr pa pb (postCode.trans (ii b inR).code.symm)
          (fun w h => keepBelow w (zoneR b inR w.toNat h)) (by omega)
    · rcases Set.mem_insert_iff.mp mem with rfl | inR
      · have := newZone w h; have := ofB w; intro hf; have := ofB w hf; omega
      · rw [zR b inR] at h; exact io b inR w h
    · rcases Set.mem_insert_iff.mp mb with rfl | inR
      · rcases Set.mem_insert_iff.mp mb' with rfl | inR'
        · exact absurd rfl ne
        · rw [zR b' inR'] at h'; have := newZone w h; have := zoneR b' inR' w h'; omega
      · rcases Set.mem_insert_iff.mp mb' with rfl | inR'
        · rw [zR b inR] at h; have := newZone w h'; have := zoneR b inR w h; omega
        · rw [zR b inR] at h; rw [zR b' inR'] at h'; exact ip b inR b' inR' ne w h h'

#print axioms MergeCtx.CoreW.after_new

/-- A uniform bound on one block-map set call. -/
def MergeCtx.setCost (c : MergeCtx) : Nat := setBodyCost c.KB (BitVec.ofNat 64 c.CB) (BitVec.ofNat 64 c.CB) + 1

set_option maxHeartbeats 4000000 in
/-- `htab_set(bouter, key, b)` with a registered inner table b: the block map stays valid with its values in
the registry, its block is kept or moves above the heap pointer, and the inner tables and outer footprint
are untouched. -/
theorem MergeCtx.CoreW.after_set {c : MergeCtx} (st : c.Static) {IB II : Nat} {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (p : BitVec 64) (R : Set (BitVec 64)) (Z : BitVec 64 → Nat × Nat)
    (core : c.CoreW IB II s p R Z) (tableArgument keyArgument valueArgument : ExpHOL 64) (key b : BitVec 64)
    (member : b ∈ R)
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word c.BO),.val (.word key),.val (.word b)])
    (cbBound : 4 * (c.NB0 + IB + 1) ≤ c.CB) (budget : c.setCost ≤ s.clock)
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
    · refine ⟨c2,k2,u2,v2,o2,op2,n2,b2,inv2,tables',?_,vt2,newTop btop,?_,?_,?_⟩
      · rcases counts with ⟨rfl,rfl⟩ | ⟨h1,h2⟩ <;> omega
      · rcases counts with ⟨rfl,rfl⟩ | ⟨h1,h2⟩ <;> omega
      · rcases capB' with rfl | h <;> (try omega)
        rcases counts with ⟨_,rfl⟩ | ⟨h1,h2⟩ <;> omega
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

#print axioms MergeCtx.CoreW.after_set

/-- Largest inner count before a union, and a uniform bound on one nested union call. -/
def MergeCtx.NIM (c : MergeCtx) : Nat := c.NI0 + c.n.toNat * c.NS

def MergeCtx.unionCost (c : MergeCtx) : Nat :=
  c.NS * (1 + 1 + ((setBodyCost c.KI (BitVec.ofNat 64 (max c.CI (4 * (c.NIM + c.NS)))) (BitVec.ofNat 64 (c.NIM + c.NS)) + 1)
    + 0) + 1) + 1

theorem MergeCtx.unionCost_mono (c : MergeCtx) (uSmall : 4 * (c.NIM + c.NS) ≤ 33806089496)
    (ciSmall : c.CI ≤ 33806089496) {F : Type} (dst stride src sn skeys sstride svals sorder count0 cap0 p : BitVec 64)
    (lo hi : Nat) (s : PanSemStateFiniteExact 64 F) (hc : cap0.toNat ≤ c.CI) (hn : count0.toNat ≤ c.NIM)
    (hs : sn.toNat ≤ c.NS) :
    sn.toNat * ((unionCtxOf c.KI dst stride src sn skeys sstride svals sorder count0 cap0 p lo hi s).stepCost + 1) + 1 ≤
      c.unionCost := by
  have m := setBodyCost_mono c.KI
    (BitVec.ofNat 64 (unionCtxOf c.KI dst stride src sn skeys sstride svals sorder count0 cap0 p lo hi s).capMax)
    (BitVec.ofNat 64 (max c.CI (4 * (c.NIM + c.NS))))
    (BitVec.ofNat 64 (count0.toNat + sn.toNat)) (BitVec.ofNat 64 (c.NIM + c.NS))
    (by
      rw [ofNat_toNat_small _ (by unfold UnionCtx.capMax unionCtxOf; simp only; omega),
        ofNat_toNat_small _ (by omega)]
      unfold UnionCtx.capMax unionCtxOf; simp only; omega)
    (by rw [ofNat_toNat_small _ (by omega),ofNat_toNat_small _ (by omega)]; omega)
    (by rw [ofNat_toNat_small _ (by omega)]; omega)
  unfold MergeCtx.unionCost UnionCtx.stepCost
  change sn.toNat * (1 + 1 + ((setBodyCost c.KI _ (BitVec.ofNat 64 (count0.toNat + sn.toNat)) + 1) + 0) + 1) + 1 ≤ _
  have := Nat.mul_le_mul hs (show 1 + 1 + ((setBodyCost c.KI
      (BitVec.ofNat 64 (unionCtxOf c.KI dst stride src sn skeys sstride svals sorder count0 cap0 p lo hi s).capMax)
      (BitVec.ofNat 64 (count0.toNat + sn.toNat)) + 1) + 0) + 1 ≤ 1 + 1 + ((setBodyCost c.KI
      (BitVec.ofNat 64 (max c.CI (4 * (c.NIM + c.NS)))) (BitVec.ofNat 64 (c.NIM + c.NS)) + 1) + 0) + 1 by omega)
  omega

#print axioms MergeCtx.unionCost_mono

set_option maxHeartbeats 4000000 in
/-- `htab_union_into(b, src)` with a registered inner table b and an outer-side source table: b stays a
valid inner table (block kept or moved above the heap pointer), everything else is untouched. -/
theorem MergeCtx.CoreW.after_union {c : MergeCtx} (st : c.Static) (uSmall : 4 * (c.NIM + c.NS) ≤ 33806089496)
    {IB II : Nat} (hII : II ≤ c.n.toNat) {F : Type}
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
    (ciBound : 4 * (c.NI0 + (II + 1) * c.NS) ≤ c.CI) (budget : c.unionCost ≤ s.clock)
    (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "htab_union_into") [dstArgument,srcArgument]) =
      (none,post)) :
    ∃ (p' : BitVec 64) (Z' : BitVec 64 → Nat × Nat), c.CoreW IB (II + 1) post p' R Z' ∧ post.locals = s.locals ∧
      s.clock ≤ post.clock + c.unionCost ∧ ∀ b' ∈ R, b' ≠ b → Z' b' = Z b' := by
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,⟨bc,bk,bu,bv,bo,bp,bn,bb,binv,bt,br,bvt,btop,bnb,bcb,bz⟩,⟨ii,io,ip⟩⟩ := core
  have ofB := st.ofBelow
  have bzB := MergeCtx.Bouter.zone_below bc bk bu bv bo bp bn bb binv btop
  have zoneR : ∀ b ∈ R, ∀ w, TZone b (Z b).1 (Z b).2 w → w < p.toNat := fun b mem w h => (ii b mem).zone_below w h
  obtain ⟨cap0,keys0,stride0,used0,vals0,order0,op0,count0,bits0,laid,tables,room,hTop,hL,hN,hC⟩ := ii b member
  have hdrLe := laid.header_le_hi
  have mulLe : II * c.NS ≤ c.n.toNat * c.NS := Nat.mul_le_mul_right _ hII
  have bud := c.unionCost_mono uSmall st.ciSmall b stride0 src sn skeys sstride svalues sorder count0 cap0 p
    (Z b).1 (Z b).2 s hC (by unfold MergeCtx.NIM; omega) snBound
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
        · change count0.toNat ≤ n'.toNat at lb; change n'.toNat ≤ count0.toNat + sn.toNat at ub
          rw [Nat.add_mul,Nat.one_mul]; omega
        · rcases capB with h | h
          · change c'.toNat ≤ cap0.toNat at h; omega
          · change n'.toNat ≤ count0.toNat + sn.toNat at ub; rw [Nat.add_mul,Nat.one_mul] at ciBound; omega
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

#print axioms MergeCtx.CoreW.after_union
end InitECandidate.Runtime
