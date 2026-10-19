import InitECandidate.Runtime.HtabReadOnly
import InitECandidate.Runtime.ScratchAllocationBodyBound
import InitECandidate.Runtime.ScratchAllocationSuccess
import InitECandidate.Runtime.ScratchAllocationGeometry
import InitECandidate.Runtime.OriginalScratchAllocationCode
import InitECandidate.Runtime.OriginalHashNewScratchCode

namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Hash-table invariant over arbitrary placements: the header and the five
arrays are aligned, pairwise disjoint regions below the arena limit whose aligned
cells are mapped. Ascending tables (HtabAligned) and descending scratch tables
are both instances. -/
structure HtabRegions {F : Type}
    (keyLength table keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F) : Prop where
  code : state.code = originalRuntimeCode
  power : capacity.toNat = 2 ^ bits
  tableAligned : table.toNat % 8 = 0
  keysAligned : keys.toNat % 8 = 0
  strideAligned : stride.toNat % 8 = 0
  valuesAligned : values.toNat % 8 = 0
  usedAligned : used.toNat % 8 = 0
  orderAligned : order.toNat % 8 = 0
  orderPosAligned : orderPos.toNat % 8 = 0
  tableEnd : table.toNat + 72 ≤ 33806089496
  keysEnd : keys.toNat + capacity.toNat * stride.toNat ≤ 33806089496
  valuesEnd : values.toNat + capacity.toNat * 8 ≤ 33806089496
  usedEnd : used.toNat + capacity.toNat ≤ 33806089496
  orderEnd : order.toNat + capacity.toNat * 8 ≤ 33806089496
  endBound : orderPos.toNat + capacity.toNat * 8 ≤ 33806089496
  sepHK : table.toNat + 72 ≤ keys.toNat ∨ keys.toNat + capacity.toNat * stride.toNat ≤ table.toNat
  sepHV : table.toNat + 72 ≤ values.toNat ∨ values.toNat + capacity.toNat * 8 ≤ table.toNat
  sepHU : table.toNat + 72 ≤ used.toNat ∨ used.toNat + capacity.toNat ≤ table.toNat
  sepHO : table.toNat + 72 ≤ order.toNat ∨ order.toNat + capacity.toNat * 8 ≤ table.toNat
  sepHP : table.toNat + 72 ≤ orderPos.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ table.toNat
  sepKU : keys.toNat + capacity.toNat * stride.toNat ≤ used.toNat ∨ used.toNat + capacity.toNat ≤ keys.toNat
  sepKO : keys.toNat + capacity.toNat * stride.toNat ≤ order.toNat ∨ order.toNat + capacity.toNat * 8 ≤ keys.toNat
  sepKP : keys.toNat + capacity.toNat * stride.toNat ≤ orderPos.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ keys.toNat
  sepVU : values.toNat + capacity.toNat * 8 ≤ used.toNat ∨ used.toNat + capacity.toNat ≤ values.toNat
  sepVO : values.toNat + capacity.toNat * 8 ≤ order.toNat ∨ order.toNat + capacity.toNat * 8 ≤ values.toNat
  sepVP : values.toNat + capacity.toNat * 8 ≤ orderPos.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ values.toNat
  sepUO : used.toNat + capacity.toNat ≤ order.toNat ∨ order.toNat + capacity.toNat * 8 ≤ used.toNat
  sepUP : used.toNat + capacity.toNat ≤ orderPos.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ used.toNat
  sepOP : order.toNat + capacity.toNat * 8 ≤ orderPos.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ order.toNat
  fits : keyLength.toNat ≤ stride.toNat
  domain : ∀ a : BitVec 64, a.toNat % 8 = 0 →
      ((table.toNat ≤ a.toNat ∧ a.toNat < table.toNat + 72) ∨
      (keys.toNat ≤ a.toNat ∧ a.toNat < keys.toNat + capacity.toNat * stride.toNat) ∨
      (values.toNat ≤ a.toNat ∧ a.toNat < values.toNat + capacity.toNat * 8) ∨
      (used.toNat ≤ a.toNat ∧ a.toNat < used.toNat + capacity.toNat) ∨
      (order.toNat ≤ a.toNat ∧ a.toNat < order.toNat + capacity.toNat * 8) ∨
      (orderPos.toNat ≤ a.toNat ∧ a.toNat < orderPos.toNat + capacity.toNat * 8)) → state.memaddrs a
  cell0 : state.memory (table + 0) = .word keyLength
  cell8 : state.memory (table + 8) = .word stride
  cell16 : state.memory (table + 16) = .word capacity
  cell24 : state.memory (table + 24) = .word count
  cell32 : state.memory (table + 32) = .word keys
  cell40 : state.memory (table + 40) = .word values
  cell48 : state.memory (table + 48) = .word used
  cell56 : state.memory (table + 56) = .word order
  cell64 : state.memory (table + 64) = .word orderPos
  agreement : count.toNat = hashOccupiedCount capacity (hashOccupancyRead state used)

/-- Bridge: every ascending aligned table is a region table. -/
theorem HtabAligned.toRegions {F : Type} {s : PanSemStateFiniteExact 64 F} {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat}
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits s) : HtabRegions keyLength table keys stride capacity used values order orderPos count bits s := by
  have hk := inv.headerKeys; have hv := inv.headerValues; have kb := inv.keysBefore; have vb := inv.valuesBefore
  have ub := inv.usedBefore; have ob := inv.orderBefore; have eb := inv.endBound
  exact {
    code := inv.code, power := inv.power, tableAligned := inv.tableAligned, keysAligned := inv.keysAligned,
    strideAligned := inv.strideAligned, valuesAligned := inv.valuesAligned, usedAligned := inv.usedAligned,
    orderAligned := inv.orderAligned, orderPosAligned := inv.orderPosAligned,
    tableEnd := by omega, keysEnd := by omega, valuesEnd := by omega, usedEnd := by omega, orderEnd := by omega,
    endBound := eb,
    sepHK := by omega, sepHV := by omega, sepHU := by omega, sepHO := by omega, sepHP := by omega, sepKU := by omega, sepKO := by omega, sepKP := by omega, sepVU := by omega, sepVO := by omega, sepVP := by omega, sepUO := by omega, sepUP := by omega, sepOP := by omega,
    fits := inv.fits,
    domain := fun a h1 h2 => inv.domain a h1 (by omega) (by omega),
    cell0 := inv.cell0, cell8 := inv.cell8, cell16 := inv.cell16, cell24 := inv.cell24, cell32 := inv.cell32,
    cell40 := inv.cell40, cell48 := inv.cell48, cell56 := inv.cell56, cell64 := inv.cell64,
    agreement := inv.agreement }

theorem HtabRegions.transfer {F G : Type} {s : PanSemStateFiniteExact 64 F} {r : PanSemStateFiniteExact 64 G} {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat}
    (inv : HtabRegions keyLength table keys stride capacity used values order orderPos count bits s) (memory : r.memory = s.memory) (addresses : r.memaddrs = s.memaddrs) (endian : r.be = s.be)
    (code : r.code = s.code) : HtabRegions keyLength table keys stride capacity used values order orderPos count bits r := by
  have read : ∀ slot, hashOccupancyRead r used slot = hashOccupancyRead s used slot := by
    intro slot; unfold hashOccupancyRead; rw [memory,addresses,endian]
  exact { inv with
    code := code.trans inv.code,
    domain := fun a h1 h2 => by rw [addresses]; exact inv.domain a h1 h2,
    cell0 := by rw [memory]; exact inv.cell0, cell8 := by rw [memory]; exact inv.cell8,
    cell16 := by rw [memory]; exact inv.cell16, cell24 := by rw [memory]; exact inv.cell24,
    cell32 := by rw [memory]; exact inv.cell32, cell40 := by rw [memory]; exact inv.cell40,
    cell48 := by rw [memory]; exact inv.cell48, cell56 := by rw [memory]; exact inv.cell56,
    cell64 := by rw [memory]; exact inv.cell64,
    agreement := by rw [inv.agreement]; exact hashOccupiedCount_congr _ _ _ (fun slot _ => (read slot).symm) }

theorem HtabRegions.header_domain {F : Type} {s : PanSemStateFiniteExact 64 F} {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat}
    (inv : HtabRegions keyLength table keys stride capacity used values order orderPos count bits s) (k : Nat) (hk : k ≤ 64) (ha : k % 8 = 0) : s.memaddrs (table + BitVec.ofNat 64 k) := by
  have te := inv.tableEnd
  have eq := word_add_toNat table k (by omega)
  have := inv.tableAligned
  exact inv.domain _ (by rw [eq]; omega) (Or.inl (by rw [eq]; omega))

theorem HtabRegions.keys_domain {F : Type} {s : PanSemStateFiniteExact 64 F} {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat}
    (inv : HtabRegions keyLength table keys stride capacity used values order orderPos count bits s) (a : BitVec 64) (al : a.toNat % 8 = 0) (lo : keys.toNat ≤ a.toNat)
    (hi : a.toNat < keys.toNat + capacity.toNat * stride.toNat) : s.memaddrs a :=
  inv.domain a al (Or.inr (Or.inl ⟨lo,hi⟩))

theorem HtabRegions.values_domain {F : Type} {s : PanSemStateFiniteExact 64 F} {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat}
    (inv : HtabRegions keyLength table keys stride capacity used values order orderPos count bits s) (a : BitVec 64) (al : a.toNat % 8 = 0) (lo : values.toNat ≤ a.toNat)
    (hi : a.toNat < values.toNat + capacity.toNat * 8) : s.memaddrs a :=
  inv.domain a al (Or.inr (Or.inr (Or.inl ⟨lo,hi⟩)))

theorem HtabRegions.used_domain {F : Type} {s : PanSemStateFiniteExact 64 F} {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat}
    (inv : HtabRegions keyLength table keys stride capacity used values order orderPos count bits s) (a : BitVec 64) (al : a.toNat % 8 = 0) (lo : used.toNat ≤ a.toNat)
    (hi : a.toNat < used.toNat + capacity.toNat) : s.memaddrs a :=
  inv.domain a al (Or.inr (Or.inr (Or.inr (Or.inl ⟨lo,hi⟩))))

theorem HtabRegions.order_domain {F : Type} {s : PanSemStateFiniteExact 64 F} {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat}
    (inv : HtabRegions keyLength table keys stride capacity used values order orderPos count bits s) (a : BitVec 64) (al : a.toNat % 8 = 0) (lo : order.toNat ≤ a.toNat)
    (hi : a.toNat < order.toNat + capacity.toNat * 8) : s.memaddrs a :=
  inv.domain a al (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨lo,hi⟩)))))

theorem HtabRegions.orderPos_domain {F : Type} {s : PanSemStateFiniteExact 64 F} {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat}
    (inv : HtabRegions keyLength table keys stride capacity used values order orderPos count bits s) (a : BitVec 64) (al : a.toNat % 8 = 0) (lo : orderPos.toNat ≤ a.toNat)
    (hi : a.toNat < orderPos.toNat + capacity.toNat * 8) : s.memaddrs a :=
  inv.domain a al (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨lo,hi⟩)))))

/-- Slot address arithmetic of a region table. -/
theorem HtabRegions.slot_toNat {F : Type} {s : PanSemStateFiniteExact 64 F} {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat}
    (inv : HtabRegions keyLength table keys stride capacity used values order orderPos count bits s) (q : BitVec 64) (inside : q.toNat < capacity.toNat) :
    (values + q * 8).toNat = values.toNat + q.toNat * 8 ∧ (order + q * 8).toNat = order.toNat + q.toNat * 8 ∧
      (orderPos + q * 8).toNat = orderPos.toNat + q.toNat * 8 ∧
      (keys + q * stride).toNat = keys.toNat + q.toNat * stride.toNat ∧
      q.toNat * stride.toNat + stride.toNat ≤ capacity.toNat * stride.toNat := by
  have ve := inv.valuesEnd; have oe := inv.orderEnd; have pe := inv.endBound; have ke := inv.keysEnd
  have mono : q.toNat * stride.toNat + stride.toNat ≤ capacity.toNat * stride.toNat := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ inside
  have eight : (8 : BitVec 64).toNat = 8 := rfl
  refine ⟨?_,?_,?_,?_,mono⟩
  · rw [word_mul_add_toNat values q 8 (by rw [eight]; omega),eight]
  · rw [word_mul_add_toNat order q 8 (by rw [eight]; omega),eight]
  · rw [word_mul_add_toNat orderPos q 8 (by rw [eight]; omega),eight]
  · exact word_mul_add_toNat keys q stride (by omega)

theorem OrderInv.of_count_zero_regions {F : Type} {s : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos : BitVec 64} {bits : Nat}
    (inv : HtabRegions keyLength table keys stride capacity used values order orderPos 0 bits s) :
    OrderInv s capacity 0 used order orderPos :=
  ⟨fun q inside occupied => absurd (hashOccupiedCount_zero_reads capacity (hashOccupancyRead s used)
    (by rw [← inv.agreement]; rfl) q inside) occupied,HashOrderEntriesBound.empty order capacity s⟩

#print axioms HtabAligned.toRegions
#print axioms HtabRegions.transfer
#print axioms HtabRegions.slot_toNat
#print axioms OrderInv.of_count_zero_regions
theorem scratchAllocationEnd_aligned (pointer size : BitVec 64) : (scratchAllocationEnd pointer size).toNat % 8 = 0 := by
  unfold scratchAllocationEnd
  rw [BitVec.toNat_and]
  have : ((0 : BitVec 64) - 8).toNat = 2 ^ 64 - 8 := by decide
  rw [this]
  generalize (pointer - size).toNat = x
  rw [← Nat.and_two_pow_sub_one_eq_mod _ 3,Nat.and_assoc,show (2 ^ 64 - 8) &&& (2 ^ 3 - 1) = 0 by decide,Nat.and_zero]

/-- A returned declared scratch allocation: the request fit above the frame,
the name holds the rounded-down new frontier, scratch_ptr moved there and
memory, other globals and locals are unchanged. -/
theorem scratch_alloc_decCall_returned {F : Type} (s post : PanSemStateFiniteExact 64 F) (name : MlS) (sizeArgument : ExpHOL 64)
    (continuation : ProgHOL 64) (pointer size frame : BitVec 64) (v : ValueHOL 64)
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [sizeArgument] =
      some [.val (.word size)])
    (code : s.code = originalRuntimeCode)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (clock : 2 ≤ s.clock)
    (run : evaluateHOLFiniteState s (.decCall name .one (ofString "scratch_alloc") [sizeArgument] continuation) =
      (some (.returned v),post)) :
    ∃ r inner : PanSemStateFiniteExact 64 F,
      r.locals.lookup name = some (.val (.word (scratchAllocationEnd pointer size))) ∧
      (∀ k, k ≠ name → r.locals.lookup k = s.locals.lookup k) ∧
      r.memory = s.memory ∧ r.memaddrs = s.memaddrs ∧ r.be = s.be ∧ r.code = s.code ∧
      r.globals = (setGlobalHOLFinite (ofString "scratch_ptr") (.val (.word (scratchAllocationEnd pointer size))) s).globals ∧
      size ≤ pointer - frame ∧ frame ≤ scratchAllocationEnd pointer size ∧ s.clock ≤ r.clock + 2 ∧
      evaluateHOLFiniteState r continuation = (some (.returned v),inner) ∧
      post.memory = inner.memory ∧ post.memaddrs = inner.memaddrs ∧ post.be = inner.be ∧ post.code = inner.code := by
  obtain ⟨values,body,callee,rs,w,bodyPost,resumed,inner,argsR,lookup,bodyRun,rm,ra,rb,rc,rg,rclk,rh,ragree,rrun,
    pm,pa,pb,pc⟩ := decCall_returned_globals run
  rw [args] at argsR
  cases argsR
  have installed : s.code.lookup (ofString "scratch_alloc") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_scratch_alloc,.one) := by
    rw [code]; exact originalRuntimeCode_scratchAllocation_lookup
  rw [pan_single_word_lookup s.code.lookup (ofString "scratch_alloc") (ofString "n")
    (sourceFunctionBody Guest.guestFn_scratch_alloc) size installed] at lookup
  cases lookup
  generalize hentry : callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n",.val (.word size))) = entry at bodyRun rclk
  have eS : entry.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)) := by rw [← hentry]; exact scratchGlobal
  have eF : entry.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by rw [← hentry]; exact frameGlobal
  have eN : entry.locals.lookup (ofString "n") = some (.val (.word size)) := by
    rw [← hentry]; simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have eCode : entry.code = originalRuntimeCode := by rw [← hentry]; exact code
  have eClock : entry.clock = s.clock - 1 := by rw [← hentry]; rfl
  obtain ⟨result,post',run',k1,k2,_,_,prop⟩ := evaluate_scratch_alloc_body_bounded entry pointer size frame eS eN eF eCode (by omega)
  rw [bodyRun] at run'
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj run'
  obtain ⟨hw,request,within⟩ := prop w rfl
  obtain ⟨post2,run2,g2,_,m2,c2,a2,_,b2,glob2⟩ := evaluate_source_scratch_alloc_success entry pointer size frame eS eN eF request within
  rw [bodyRun] at run2
  obtain ⟨_,rfl⟩ := Prod.mk.inj run2
  subst hw
  refine ⟨resumed,inner,rh,ragree,rm.trans (m2.trans (by rw [← hentry]; rfl)),ra.trans (a2.trans (by rw [← hentry]; rfl)),
    rb.trans (b2.trans (by rw [← hentry]; rfl)),rc.trans (c2.trans (by rw [← hentry]; rfl)),?_,request,within,?_,rrun,pm,pa,pb,pc⟩
  · rw [rg,glob2,← hentry]; rfl
  · rw [rclk k2]; omega

#print axioms scratch_alloc_decCall_returned

theorem source_htabNewScratch_body : sourceFunctionBody Guest.guestFn_htab_new_scratch =
    .decCall (ofString "t") .one (ofString "scratch_alloc") [.const 72]
    (.dec (ofString "stride") .one htabNewStrideExpression
    (.seq (.store (hashLocalAddress (ofString "t") 0) (.var .local (ofString "key_len")))
    (.seq (.store (hashLocalAddress (ofString "t") 8) (.var .local (ofString "stride")))
    (.seq (.store (hashLocalAddress (ofString "t") 16) (.var .local (ofString "cap")))
    (.seq (.store (hashLocalAddress (ofString "t") 24) (.const 0))
    (.decCall (ofString "keys") .one (ofString "scratch_alloc") [.panop .mul [.var .local (ofString "cap"),.var .local (ofString "stride")]]
    (.seq (.store (hashLocalAddress (ofString "t") 32) (.var .local (ofString "keys")))
    (.decCall (ofString "vals") .one (ofString "scratch_alloc") [.panop .mul [.var .local (ofString "cap"),.const 8]]
    (.seq (.store (hashLocalAddress (ofString "t") 40) (.var .local (ofString "vals")))
    (.decCall (ofString "used") .one (ofString "scratch_alloc") [.var .local (ofString "cap")]
    (.seq (.call (some (none,none)) (ofString "memzero") [.var .local (ofString "used"),.var .local (ofString "cap")])
    (.seq (.store (hashLocalAddress (ofString "t") 48) (.var .local (ofString "used")))
    (.decCall (ofString "order") .one (ofString "scratch_alloc") [.panop .mul [.var .local (ofString "cap"),.const 8]]
    (.seq (.store (hashLocalAddress (ofString "t") 56) (.var .local (ofString "order")))
    (.decCall (ofString "order_pos") .one (ofString "scratch_alloc") [.panop .mul [.var .local (ofString "cap"),.const 8]]
    (.seq (.store (hashLocalAddress (ofString "t") 64) (.var .local (ofString "order_pos")))
    (.return (.var .local (ofString "t"))))))))))))))))))) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl


theorem scratch_step_layout (pointer size frame : BitVec 64) (frLe : frame.toNat ≤ pointer.toNat)
    (request : size ≤ pointer - frame) (within : frame ≤ scratchAllocationEnd pointer size) :
    (scratchAllocationEnd pointer size).toNat + size.toNat ≤ pointer.toNat ∧
      (scratchAllocationEnd pointer size).toNat % 8 = 0 ∧ frame.toNat ≤ (scratchAllocationEnd pointer size).toNat := by
  have r := BitVec.le_def.mp request
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr frLe)] at r
  exact ⟨scratchAllocationEnd_before pointer size (by omega),scratchAllocationEnd_aligned pointer size,BitVec.le_def.mp within⟩

theorem htabNewScratch_returned_regions {F : Type} (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (keyLength capacity : BitVec 64) (bits : Nat) (code : state.code = originalRuntimeCode)
    (keyLocal : state.locals.lookup (ofString "key_len") = some (.val (.word keyLength)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (sp fr : BitVec 64)
    (scratchG : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp)))
    (frameG : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fr)))
    (frLe : fr.toNat ≤ sp.toNat) (spInside : sp.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → fr.toNat ≤ a.toNat → a.toNat < sp.toNat → state.memaddrs a)
    (power : capacity.toNat = 2 ^ bits) (klenSmall : keyLength.toNat < 2 ^ 28)
    (budget : capacity.toNat + 13 ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_new_scratch) = (some (.returned v),post)) :
    ∃ pointer keys stride used values order orderPos : BitVec 64, v = .val (.word pointer) ∧
      HtabRegions keyLength pointer keys stride capacity used values order orderPos 0 bits post ∧
      OrderInv post capacity 0 used order orderPos ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      fr.toNat ≤ orderPos.toNat ∧ pointer.toNat + 72 ≤ sp.toNat ∧
      ∀ w : BitVec 64, (w.toNat < fr.toNat ∨ sp.toNat ≤ w.toNat) → post.memory w = state.memory w := by
  have small : keyLength.toNat ≤ 33806089496 := by omega
  rw [source_htabNewScratch_body] at run
  -- the header allocation
  obtain ⟨r1,i1,n1,o1,m1,a1,b1,c1,h1,q1,f1,k1,run1,pm1,pa1,pb1,pc1⟩ := scratch_alloc_decCall_returned state post _ (.const 72) _
    sp 72 fr v rfl code scratchG frameG (by omega) run
  have L1' := scratch_step_layout sp 72 fr frLe q1 f1
  obtain ⟨L1a,L1b,L1c⟩ := L1'
  rw [show (72 : BitVec 64).toNat = 72 from rfl] at L1a
  generalize hpt : scratchAllocationEnd sp 72 = pointer at *
  have sG1 : r1.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)) := by
    rw [h1]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have fG1 : r1.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fr)) := by
    rw [h1]; simp (config := {decide := true}) [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,frameG]
  obtain ⟨sv,i2,se,run2,m2,a2,b2,c2⟩ := dec_returned_state run1
  rw [eval_htabNew_stride r1 keyLength ((o1 _ (by decide)).trans keyLocal)] at se
  cases se
  generalize hR2 : setVarHOLFinite (ofString "stride") (.val (.word (allocationEnd 0 keyLength))) r1 = R2 at run2
  have r2L : ∀ k, k ≠ ofString "stride" → k ≠ ofString "t" → R2.locals.lookup k = state.locals.lookup k := by
    intro k n1' n2'; rw [← hR2]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm n1']; exact o1 k n2'
  have r2T : R2.locals.lookup (ofString "t") = some (.val (.word pointer)) := by
    rw [← hR2]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]; exact n1
  have r2S : R2.locals.lookup (ofString "stride") = some (.val (.word (allocationEnd 0 keyLength))) := by
    rw [← hR2]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have r2K := (r2L _ (by decide) (by decide)).trans keyLocal
  have r2C := (r2L _ (by decide) (by decide)).trans capLocal
  have r2F : R2.memory = state.memory ∧ R2.memaddrs = state.memaddrs ∧ R2.be = state.be ∧ R2.code = state.code ∧
      R2.clock = r1.clock ∧ R2.globals = r1.globals := by
    rw [← hR2]; exact ⟨m1,a1,b1,c1,rfl,rfl⟩
  -- four header stores
  have run3 := store_local_seq_returned R2 i2 _ 0 pointer keyLength _ r2T (eval_delVar R2 _ _ r2K) run2
  have run4 := store_local_seq_returned (sourceWriteWord R2 (pointer + 0) keyLength) i2 _ 8 pointer
    (allocationEnd 0 keyLength) _ (by exact r2T) (eval_delVar _ _ _ (by exact r2S)) run3
  have run5 := store_local_seq_returned (sourceWriteWord (sourceWriteWord R2 (pointer + 0) keyLength) (pointer + 8)
    (allocationEnd 0 keyLength)) i2 _ 16 pointer capacity _ (by exact r2T) (eval_delVar _ _ _ (by exact r2C)) run4
  have run6 := store_local_seq_returned (sourceWriteWord (sourceWriteWord (sourceWriteWord R2 (pointer + 0) keyLength)
    (pointer + 8) (allocationEnd 0 keyLength)) (pointer + 16) capacity) i2 _ 24 pointer 0 _ (by exact r2T)
    (eval_const_word _ 0) run5
  generalize hW : sourceWriteWord (sourceWriteWord (sourceWriteWord (sourceWriteWord R2 (pointer + 0) keyLength)
    (pointer + 8) (allocationEnd 0 keyLength)) (pointer + 16) capacity) (pointer + 24) 0 = W at run6
  have wF : W.locals = R2.locals ∧ W.memaddrs = state.memaddrs ∧ W.be = state.be ∧ W.code = state.code ∧
      W.clock = r1.clock ∧ W.globals = r1.globals ∧
      ∀ x, W.memory x = if x = pointer + 24 then .word 0 else if x = pointer + 16 then .word capacity else
        if x = pointer + 8 then .word (allocationEnd 0 keyLength) else if x = pointer + 0 then .word keyLength else
        state.memory x := by
    rw [← hW]; exact ⟨rfl,r2F.2.1,r2F.2.2.1,r2F.2.2.2.1,r2F.2.2.2.2.1,r2F.2.2.2.2.2,fun x => by simp only [sourceWriteWord]; rw [r2F.1]⟩
  obtain ⟨wL,wA,wB,wCo,wK,wG,wM⟩ := wF
  have stride := allocationEnd_covers 0 keyLength (by change 0 + keyLength.toNat ≤ 33806089496; omega)
  change 0 + keyLength.toNat ≤ _ ∧ _ < 0 + keyLength.toNat + 8 ∧ _ % 8 = 0 at stride
  have hdr : ∀ k : Nat, k ≤ 72 → (pointer + BitVec.ofNat 64 k).toNat = pointer.toNat + k :=
    fun k hk => word_add_toNat pointer k (by omega)
  -- keys
  obtain ⟨r3,i3,n3,o3,m3,a3,b3,c3,h3,q3,f3,k3,run7,pm3,pa3,pb3,pc3⟩ := scratch_alloc_decCall_returned W i2 _ _ _
    pointer (capacity * allocationEnd 0 keyLength) fr v
    (eval_mul_local_local W _ _ capacity _ (by rw [wL]; exact r2C) (by rw [wL]; exact r2S)) (wCo.trans code)
    (by rw [wG]; exact sG1) (by rw [wG]; exact fG1) (by rw [wK]; omega) run6
  have L2' := scratch_step_layout pointer _ fr L1c q3 f3
  obtain ⟨L2a,L2b,L2c⟩ := L2'
  generalize hq2 : scratchAllocationEnd pointer (capacity * allocationEnd 0 keyLength) = p1 at *
  have sG3 : r3.globals.lookup (ofString "scratch_ptr") = some (.val (.word p1)) := by
    rw [h3]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have fG3 : r3.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fr)) := by
    rw [h3]; simp (config := {decide := true}) [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]; rw [wG]; exact fG1
  have r3T : r3.locals.lookup (ofString "t") = some (.val (.word pointer)) := by rw [o3 _ (by decide),wL]; exact r2T
  have r3C : r3.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by rw [o3 _ (by decide),wL]; exact r2C
  have run8 := store_local_seq_returned r3 i3 _ 32 pointer p1 _ r3T (eval_delVar _ _ _ n3) run7
  generalize hX1 : sourceWriteWord r3 (pointer + 32) p1 = X1 at run8
  have x1F : X1.locals = r3.locals ∧ X1.memaddrs = state.memaddrs ∧ X1.be = state.be ∧ X1.code = state.code ∧
      X1.clock = r3.clock ∧ X1.globals = r3.globals ∧
      ∀ x, X1.memory x = if x = pointer + 32 then .word p1 else W.memory x := by
    rw [← hX1]; exact ⟨rfl,a3.trans wA,b3.trans wB,c3.trans wCo,rfl,rfl,fun x => by simp only [sourceWriteWord]; rw [m3]⟩
  obtain ⟨x1L,x1A,x1B,x1Co,x1K,x1G,x1M⟩ := x1F
  -- values
  obtain ⟨r4,i4,n4,o4,m4,a4,b4,c4,h4,q4,f4,k4,run9,pm4,pa4,pb4,pc4⟩ := scratch_alloc_decCall_returned X1 i3 _ _ _
    p1 (capacity * 8) fr v
    (eval_mul_local_const X1 _ capacity 8 (by rw [x1L]; exact r3C)) (x1Co.trans code)
    (by rw [x1G]; exact sG3) (by rw [x1G]; exact fG3) (by rw [x1K]; omega) run8
  have L3' := scratch_step_layout p1 _ fr L2c q4 f4
  obtain ⟨L3a,L3b,L3c⟩ := L3'
  generalize hq3 : scratchAllocationEnd p1 (capacity * 8) = p2 at *
  have sG4 : r4.globals.lookup (ofString "scratch_ptr") = some (.val (.word p2)) := by
    rw [h4]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have fG4 : r4.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fr)) := by
    rw [h4]; simp (config := {decide := true}) [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]; rw [x1G]; exact fG3
  have r4T : r4.locals.lookup (ofString "t") = some (.val (.word pointer)) := by rw [o4 _ (by decide),x1L]; exact r3T
  have r4C : r4.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by rw [o4 _ (by decide),x1L]; exact r3C
  have run10 := store_local_seq_returned r4 i4 _ 40 pointer _ _ r4T (eval_delVar _ _ _ n4) run9
  generalize hX2 : sourceWriteWord r4 (pointer + 40) p2 = X2 at run10
  have x2F : X2.locals = r4.locals ∧ X2.memaddrs = state.memaddrs ∧ X2.be = state.be ∧ X2.code = state.code ∧
      X2.clock = r4.clock ∧ X2.globals = r4.globals ∧
      ∀ x, X2.memory x = if x = pointer + 40 then .word p2 else X1.memory x := by
    rw [← hX2]; exact ⟨rfl,a4.trans x1A,b4.trans x1B,c4.trans x1Co,rfl,rfl,fun x => by simp only [sourceWriteWord]; rw [m4]⟩
  obtain ⟨x2L,x2A,x2B,x2Co,x2K,x2G,x2M⟩ := x2F
  generalize hS : allocationEnd 0 keyLength = Sd at *
  -- the occupancy array and its zeroing
  obtain ⟨r5,i5,n5,o5,m5,a5,b5,c5,h5,q5,f5,k5,run11,pm5,pa5,pb5,pc5⟩ := scratch_alloc_decCall_returned X2 i4 _ _ _ p2 capacity fr v
    (eval_local_single X2 _ capacity (by rw [x2L]; exact r4C)) (x2Co.trans code) (by rw [x2G]; exact sG4) (by rw [x2G]; exact fG4)
    (by rw [x2K]; omega) run10
  have L4' := scratch_step_layout p2 _ fr L3c q5 f5
  obtain ⟨L4a,L4b,L4c⟩ := L4'
  generalize hq4 : scratchAllocationEnd p2 capacity = p3 at *
  have sG5 : r5.globals.lookup (ofString "scratch_ptr") = some (.val (.word p3)) := by
    rw [h5]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have fG5 : r5.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fr)) := by
    rw [h5]; simp (config := {decide := true}) [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]; rw [x2G]; exact fG4
  have capSmall : capacity.toNat ≤ 33806089496 := by omega
  have sdLe : Sd.toNat ≤ 2 ^ 28 + 8 := by have := stride.2.1; omega
  have keysSize : (capacity * Sd).toNat = capacity.toNat * Sd.toNat :=
    BitVec.toNat_mul_of_lt (Nat.lt_of_le_of_lt (Nat.mul_le_mul capSmall sdLe) (by decide))
  have eightSize : (capacity * 8).toNat = capacity.toNat * 8 := BitVec.toNat_mul_of_lt (by change _ * 8 < _; omega)
  have r5T : r5.locals.lookup (ofString "t") = some (.val (.word pointer)) := by rw [o5 _ (by decide),x2L]; exact r4T
  have r5C : r5.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by rw [o5 _ (by decide),x2L]; exact r4C
  have zeroArgs : evalListHOLFinite r5 (h := fun a => Classical.propDecidable (r5.memaddrs a))
      [.var .local (ofString "used"),.var .local (ofString "cap")] = some [.val (.word p3),.val (.word capacity)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,n5,r5C]
  have r5Code : r5.code = originalRuntimeCode := (c5.trans x2Co).trans code
  obtain ⟨mz,zeroRun,_,zCost,_,zGl,_,zAddr,zBe,zLocals,zocc⟩ := evaluate_memzero_aligned_call_cells r5 _ _ p3 capacity zeroArgs
    r5Code (by omega) (by omega) L4b
    (by
      intro offset inside
      rw [a5,x2A]
      have align := byteAlign_toNat (p3 + BitVec.ofNat 64 offset)
      have sum : (p3 + BitVec.ofNat 64 offset).toNat = p3.toNat + offset := word_add_toNat p3 offset (by omega)
      rw [sum] at align
      exact arena _ (by rw [align]; omega) (by rw [align]; omega) (by rw [align]; omega))
  obtain ⟨Z,zRun,run12⟩ := seq_returned_of_nonreturning_first (fun v => evaluate_noTopReturn _ rfl r5 v) run11
  have zEq : Z = mz := congrArg Prod.snd (zRun.symm.trans zeroRun)
  subst zEq
  have zFrame : ∀ watched : BitVec 64, (watched.toNat < p3.toNat ∨ p3.toNat + capacity.toNat ≤ watched.toNat) →
      Z.memory watched = X2.memory watched := by
    intro watched outside
    rw [(memzero_call_normal_memory r5 Z _ p3 capacity watched zeroArgs r5Code L4b (by omega) outside zRun).1,m5]
  have zMeta := evaluateHOLFiniteState_metadata r5 (.call (some (none,none)) (ofString "memzero")
    [.var .local (ofString "used"),.var .local (ofString "cap")])
  rw [zRun] at zMeta
  have zT : Z.locals.lookup (ofString "t") = some (.val (.word pointer)) := by rw [zLocals]; exact r5T
  have zC : Z.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by rw [zLocals]; exact r5C
  have zU : Z.locals.lookup (ofString "used") = some (.val (.word p3)) := by rw [zLocals]; exact n5
  have run13 := store_local_seq_returned Z i5 _ 48 pointer p3 _ zT (eval_delVar _ _ _ zU) run12
  generalize hX3 : sourceWriteWord Z (pointer + 48) p3 = X3 at run13
  have x3F : X3.locals = Z.locals ∧ X3.memaddrs = state.memaddrs ∧ X3.be = state.be ∧ X3.code = originalRuntimeCode ∧
      X3.clock = Z.clock ∧ X3.globals = Z.globals ∧
      ∀ x, X3.memory x = if x = pointer + 48 then .word p3 else Z.memory x := by
    rw [← hX3]; exact ⟨rfl,zAddr.trans (a5.trans x2A),zBe.trans (b5.trans x2B),zMeta.1.trans r5Code,rfl,rfl,fun _ => rfl⟩
  obtain ⟨x3L,x3A,x3B,x3Co,x3K,x3G,x3M⟩ := x3F
  have x3S : X3.globals.lookup (ofString "scratch_ptr") = some (.val (.word p3)) := by rw [x3G,zGl]; exact sG5
  have x3Fr : X3.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fr)) := by rw [x3G,zGl]; exact fG5
  have x3T : X3.locals.lookup (ofString "t") = some (.val (.word pointer)) := by rw [x3L]; exact zT
  have x3C : X3.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by rw [x3L]; exact zC
  -- order
  obtain ⟨r6,i6,n6,o6,m6,a6,b6,c6,h6,q6,f6,k6,run14,pm6,pa6,pb6,pc6⟩ := scratch_alloc_decCall_returned X3 i5 _ _ _ p3 (capacity * 8) fr v
    (eval_mul_local_const X3 _ capacity 8 x3C) x3Co x3S x3Fr (by rw [x3K]; omega) run13
  have L5' := scratch_step_layout p3 _ fr L4c q6 f6
  obtain ⟨L5a,L5b,L5c⟩ := L5'
  generalize hq5 : scratchAllocationEnd p3 (capacity * 8) = p4 at *
  have sG6 : r6.globals.lookup (ofString "scratch_ptr") = some (.val (.word p4)) := by
    rw [h6]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have fG6 : r6.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fr)) := by
    rw [h6]; simp (config := {decide := true}) [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]; exact x3Fr
  have r6T : r6.locals.lookup (ofString "t") = some (.val (.word pointer)) := by rw [o6 _ (by decide)]; exact x3T
  have r6C : r6.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by rw [o6 _ (by decide)]; exact x3C
  have run15 := store_local_seq_returned r6 i6 _ 56 pointer p4 _ r6T (eval_delVar _ _ _ n6) run14
  generalize hX4 : sourceWriteWord r6 (pointer + 56) p4 = X4 at run15
  have x4F : X4.locals = r6.locals ∧ X4.memaddrs = state.memaddrs ∧ X4.be = state.be ∧ X4.code = originalRuntimeCode ∧
      X4.clock = r6.clock ∧ X4.globals = r6.globals ∧
      ∀ x, X4.memory x = if x = pointer + 56 then .word p4 else X3.memory x := by
    rw [← hX4]; exact ⟨rfl,a6.trans x3A,b6.trans x3B,c6.trans x3Co,rfl,rfl,fun x => by simp only [sourceWriteWord]; rw [m6]⟩
  obtain ⟨x4L,x4A,x4B,x4Co,x4K,x4G,x4M⟩ := x4F
  -- order positions
  obtain ⟨r7,i7,n7,o7,m7,a7,b7,c7,h7,q7,f7,k7,run16,pm7,pa7,pb7,pc7⟩ := scratch_alloc_decCall_returned X4 i6 _ _ _ p4 (capacity * 8) fr v
    (eval_mul_local_const X4 _ capacity 8 (by rw [x4L]; exact r6C)) x4Co (by rw [x4G]; exact sG6) (by rw [x4G]; exact fG6)
    (by rw [x4K]; omega) run15
  have L6' := scratch_step_layout p4 _ fr L5c q7 f7
  obtain ⟨L6a,L6b,L6c⟩ := L6'
  generalize hq6 : scratchAllocationEnd p4 (capacity * 8) = p5 at *
  have r7T : r7.locals.lookup (ofString "t") = some (.val (.word pointer)) := by rw [o7 _ (by decide),x4L]; exact r6T
  have run17 := store_local_seq_returned r7 i7 _ 64 pointer p5 _ r7T (eval_delVar _ _ _ n7) run16
  generalize hX5 : sourceWriteWord r7 (pointer + 64) p5 = X5 at run17
  have x5F : X5.locals = r7.locals ∧ X5.memaddrs = state.memaddrs ∧ X5.be = state.be ∧ X5.code = originalRuntimeCode ∧
      ∀ x, X5.memory x = if x = pointer + 64 then .word p5 else X4.memory x := by
    rw [← hX5]; exact ⟨rfl,a7.trans x4A,b7.trans x4B,c7.trans x4Co,fun x => by simp only [sourceWriteWord]; rw [m7]⟩
  obtain ⟨x5L,x5A,x5B,x5Co,x5M⟩ := x5F
  have x5T : X5.locals.lookup (ofString "t") = some (.val (.word pointer)) := by rw [x5L]; exact r7T
  have value := return_local_word X5 i7 _ pointer v x5T run17
  obtain ⟨rm,ra,rb,rc⟩ := return_local_state X5 i7 _ pointer v x5T run17
  have t0 : (pointer + 0 : BitVec 64).toNat = pointer.toNat + 0 := hdr 0 (by omega)
  have t8 : (pointer + 8 : BitVec 64).toNat = pointer.toNat + 8 := hdr 8 (by omega)
  have t16 : (pointer + 16 : BitVec 64).toNat = pointer.toNat + 16 := hdr 16 (by omega)
  have t24 : (pointer + 24 : BitVec 64).toNat = pointer.toNat + 24 := hdr 24 (by omega)
  have t32 : (pointer + 32 : BitVec 64).toNat = pointer.toNat + 32 := hdr 32 (by omega)
  have t40 : (pointer + 40 : BitVec 64).toNat = pointer.toNat + 40 := hdr 40 (by omega)
  have t48 : (pointer + 48 : BitVec 64).toNat = pointer.toNat + 48 := hdr 48 (by omega)
  have t56 : (pointer + 56 : BitVec 64).toNat = pointer.toNat + 56 := hdr 56 (by omega)
  have t64 : (pointer + 64 : BitVec 64).toNat = pointer.toNat + 64 := hdr 64 (by omega)
  rw [keysSize] at L2a
  rw [eightSize] at L3a L5a L6a
  have postMem : post.memory = X5.memory :=
    pm1.trans (m2.trans (pm3.trans (pm4.trans (pm5.trans (pm6.trans (pm7.trans rm))))))
  have postAddr : post.memaddrs = state.memaddrs :=
    pa1.trans (a2.trans (pa3.trans (pa4.trans (pa5.trans (pa6.trans (pa7.trans (ra.trans x5A)))))))
  have postBe : post.be = state.be :=
    pb1.trans (b2.trans (pb3.trans (pb4.trans (pb5.trans (pb6.trans (pb7.trans (rb.trans x5B)))))))
  have postCode : post.code = originalRuntimeCode :=
    pc1.trans (c2.trans (pc3.trans (pc4.trans (pc5.trans (pc6.trans (pc7.trans (rc.trans x5Co)))))))
  have byteNat : ∀ q : BitVec 64, q.toNat < capacity.toNat → (panByteAlignHOL (p3 + q)).toNat = (p3.toNat + q.toNat) / 8 * 8 := by
    intro q inside
    rw [byteAlign_toNat,BitVec.toNat_add_of_lt (by omega)]
  have byteSame : ∀ q : BitVec 64, q.toNat < capacity.toNat →
      post.memory (panByteAlignHOL (p3 + q)) = Z.memory (panByteAlignHOL (p3 + q)) := by
    intro q inside
    have qb := byteNat q inside
    rw [postMem,x5M,if_neg (word_ne_of_toNat (by rw [qb,t64]; omega)),x4M,if_neg (word_ne_of_toNat (by rw [qb,t56]; omega)),
      x3M,if_neg (word_ne_of_toNat (by rw [qb,t48]; omega))]
  have reads : ∀ q : BitVec 64, q.toNat < capacity.toNat → hashOccupancyRead post p3 q = hashOccupancyRead Z p3 q :=
    fun q inside => occupancyRead_congr_at post Z p3 q (byteSame q inside)
      (postAddr.trans (zAddr.trans (a5.trans x2A)).symm) (postBe.trans (zBe.trans (b5.trans x2B)).symm)
  have inv : HtabRegions keyLength pointer p1 Sd capacity p3 p2 p4 p5 0 bits post := {
    code := postCode
    power := power
    tableAligned := L1b
    keysAligned := L2b
    strideAligned := stride.2.2
    valuesAligned := L3b
    usedAligned := L4b
    orderAligned := L5b
    orderPosAligned := L6b
    tableEnd := by omega, keysEnd := by omega, valuesEnd := by omega, usedEnd := by omega, orderEnd := by omega,
    endBound := by omega,
    sepHK := by omega, sepHV := by omega, sepHU := by omega, sepHO := by omega, sepHP := by omega,
    sepKU := by omega, sepKO := by omega, sepKP := by omega, sepVU := by omega, sepVO := by omega,
    sepVP := by omega, sepUO := by omega, sepUP := by omega, sepOP := by omega
    fits := by omega
    domain := fun a h1' h2' => by rw [postAddr]; exact arena a h1' (by omega) (by omega)
    cell0 := by rw [postMem,x5M,if_neg (word_ne_of_toNat (by rw [t0,t64]; omega)),x4M,if_neg (word_ne_of_toNat (by rw [t0,t56]; omega)),x3M,if_neg (word_ne_of_toNat (by rw [t0,t48]; omega)),zFrame _ (by rw [t0]; omega),x2M,if_neg (word_ne_of_toNat (by rw [t0,t40]; omega)),x1M,if_neg (word_ne_of_toNat (by rw [t0,t32]; omega)),wM,if_neg (word_ne_of_toNat (by rw [t0,t24]; omega)),if_neg (word_ne_of_toNat (by rw [t0,t16]; omega)),if_neg (word_ne_of_toNat (by rw [t0,t8]; omega)),if_pos rfl]
    cell8 := by rw [postMem,x5M,if_neg (word_ne_of_toNat (by rw [t8,t64]; omega)),x4M,if_neg (word_ne_of_toNat (by rw [t8,t56]; omega)),x3M,if_neg (word_ne_of_toNat (by rw [t8,t48]; omega)),zFrame _ (by rw [t8]; omega),x2M,if_neg (word_ne_of_toNat (by rw [t8,t40]; omega)),x1M,if_neg (word_ne_of_toNat (by rw [t8,t32]; omega)),wM,if_neg (word_ne_of_toNat (by rw [t8,t24]; omega)),if_neg (word_ne_of_toNat (by rw [t8,t16]; omega)),if_pos rfl]
    cell16 := by rw [postMem,x5M,if_neg (word_ne_of_toNat (by rw [t16,t64]; omega)),x4M,if_neg (word_ne_of_toNat (by rw [t16,t56]; omega)),x3M,if_neg (word_ne_of_toNat (by rw [t16,t48]; omega)),zFrame _ (by rw [t16]; omega),x2M,if_neg (word_ne_of_toNat (by rw [t16,t40]; omega)),x1M,if_neg (word_ne_of_toNat (by rw [t16,t32]; omega)),wM,if_neg (word_ne_of_toNat (by rw [t16,t24]; omega)),if_pos rfl]
    cell24 := by rw [postMem,x5M,if_neg (word_ne_of_toNat (by rw [t24,t64]; omega)),x4M,if_neg (word_ne_of_toNat (by rw [t24,t56]; omega)),x3M,if_neg (word_ne_of_toNat (by rw [t24,t48]; omega)),zFrame _ (by rw [t24]; omega),x2M,if_neg (word_ne_of_toNat (by rw [t24,t40]; omega)),x1M,if_neg (word_ne_of_toNat (by rw [t24,t32]; omega)),wM,if_pos rfl]
    cell32 := by rw [postMem,x5M,if_neg (word_ne_of_toNat (by rw [t32,t64]; omega)),x4M,if_neg (word_ne_of_toNat (by rw [t32,t56]; omega)),x3M,if_neg (word_ne_of_toNat (by rw [t32,t48]; omega)),zFrame _ (by rw [t32]; omega),x2M,if_neg (word_ne_of_toNat (by rw [t32,t40]; omega)),x1M,if_pos rfl]
    cell40 := by rw [postMem,x5M,if_neg (word_ne_of_toNat (by rw [t40,t64]; omega)),x4M,if_neg (word_ne_of_toNat (by rw [t40,t56]; omega)),x3M,if_neg (word_ne_of_toNat (by rw [t40,t48]; omega)),zFrame _ (by rw [t40]; omega),x2M,if_pos rfl]
    cell48 := by rw [postMem,x5M,if_neg (word_ne_of_toNat (by rw [t48,t64]; omega)),x4M,if_neg (word_ne_of_toNat (by rw [t48,t56]; omega)),x3M,if_pos rfl]
    cell56 := by rw [postMem,x5M,if_neg (word_ne_of_toNat (by rw [t56,t64]; omega)),x4M,if_pos rfl]
    cell64 := by rw [postMem,x5M,if_pos rfl]
    agreement := by rw [hashOccupiedCount_congr capacity _ _ reads,zocc]; rfl }
  refine ⟨pointer,p1,Sd,p3,p2,p4,p5,value,inv,OrderInv.of_count_zero_regions inv,postAddr,postBe,L6c,L1a,fun w below => ?_⟩
  rw [postMem,x5M,if_neg (word_ne_of_toNat (by rw [t64]; omega)),x4M,if_neg (word_ne_of_toNat (by rw [t56]; omega)),
    x3M,if_neg (word_ne_of_toNat (by rw [t48]; omega)),zFrame w (by omega),x2M,
    if_neg (word_ne_of_toNat (by rw [t40]; omega)),x1M,if_neg (word_ne_of_toNat (by rw [t32]; omega)),wM,
    if_neg (word_ne_of_toNat (by rw [t24]; omega)),if_neg (word_ne_of_toNat (by rw [t16]; omega)),
    if_neg (word_ne_of_toNat (by rw [t8]; omega)),if_neg (word_ne_of_toNat (by rw [t0]; omega))]

#print axioms htabNewScratch_returned_regions

#print axioms scratch_alloc_decCall_returned

/-- The scratch constructor contract from an actual call entry on word arguments. -/
theorem htabNewScratch_entry_regions {F : Type} (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (keyLength capacity : BitVec 64) (bits : Nat) (code : state.code = originalRuntimeCode) (sp fr : BitVec 64)
    (scratchG : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp)))
    (frameG : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fr)))
    (frLe : fr.toNat ≤ sp.toNat) (spInside : sp.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → fr.toNat ≤ a.toNat → a.toNat < sp.toNat → state.memaddrs a)
    (power : capacity.toNat = 2 ^ bits) (klenSmall : keyLength.toNat < 2 ^ 28)
    (budget : capacity.toNat + 14 ≤ state.clock)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite state
      ((HolFiniteMapExact.empty.update (ofString "key_len",.val (.word keyLength))).update (ofString "cap",.val (.word capacity))))
      (sourceFunctionBody Guest.guestFn_htab_new_scratch) = (some (.returned v),post)) :
    ∃ pointer keys stride used values order orderPos : BitVec 64, v = .val (.word pointer) ∧
      HtabRegions keyLength pointer keys stride capacity used values order orderPos 0 bits post ∧
      OrderInv post capacity 0 used order orderPos ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      fr.toNat ≤ orderPos.toNat ∧ pointer.toNat + 72 ≤ sp.toNat ∧
      ∀ w : BitVec 64, (w.toNat < fr.toNat ∨ sp.toNat ≤ w.toNat) → post.memory w = state.memory w :=
  htabNewScratch_returned_regions (callEntryStateHOLFinite state
      ((HolFiniteMapExact.empty.update (ofString "key_len",.val (.word keyLength))).update (ofString "cap",.val (.word capacity))))
    post v keyLength capacity bits (by exact code)
    (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) sp fr (by exact scratchG) (by exact frameG)
    frLe spInside (fun a h1 h2 h3 => by exact arena a h1 h2 h3) power klenSmall
    (by change _ ≤ state.clock - 1; omega) run

theorem htabNewScratch_installed {F : Type} (state : PanSemStateFiniteExact 64 F) (keyLength capacity : BitVec 64)
    (code : state.code = originalRuntimeCode) :
    lookupCodeHOLFinite state.code.lookup (ofString "htab_new_scratch") [.val (.word keyLength),.val (.word capacity)] =
      some (sourceFunctionBody Guest.guestFn_htab_new_scratch,
        (HolFiniteMapExact.empty.update (ofString "key_len",.val (.word keyLength))).update (ofString "cap",.val (.word capacity)),
        .one) :=
  pan_two_word_lookup state.code.lookup (ofString "htab_new_scratch") (ofString "key_len") (ofString "cap")
    (sourceFunctionBody Guest.guestFn_htab_new_scratch) keyLength capacity (by decide)
    (by rw [code]; exact originalRuntimeCode_htabNewScratch_lookup)

#print axioms htabNewScratch_entry_regions
#print axioms htabNewScratch_installed
#print axioms scratchAllocationEnd_aligned
#print axioms scratch_step_layout
end InitECandidate.Runtime
