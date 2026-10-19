import InitECandidate.Runtime.HtabDelBound
import InitECandidate.Runtime.HashOrderEntriesBound
import InitECandidate.Runtime.HashEmptyEntryInvariants
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Order invariant of an aligned table: occupied slots have in-table order
positions and live order entries are in-table slots. -/
def OrderInv {F : Type} (s : PanSemStateFiniteExact 64 F) (capacity count used order orderPos : BitVec 64) : Prop :=
  OrderPosBounded s capacity used orderPos ∧ HashOrderEntriesBound order capacity count s

/-- An aligned table at count zero has no occupied slot and no live order entry. -/
theorem OrderInv.of_count_zero {F : Type} {s : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos : BitVec 64} {bits : Nat}
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos 0 bits s) :
    OrderInv s capacity 0 used order orderPos := by
  refine ⟨fun q inside occupied => absurd (hashOccupiedCount_zero_reads capacity (hashOccupancyRead s used)
    (by rw [← inv.agreement]; rfl) q inside) occupied,HashOrderEntriesBound.empty order capacity s⟩

#print axioms OrderInv.of_count_zero

/-- The insertion tail writes the slot into order[count] and count into order_pos[slot]. -/
theorem HashInsertTailReady.run_tables {F : Type}
    {capacity used table values value order orderPos count index cell : BitVec 64}
    {state : PanSemStateFiniteExact 64 F}
    (ready : HashInsertTailReady capacity used table values value order orderPos count index cell state)
    (countOrder : order + count * 8 ≠ table + 24) (countPos : orderPos + index * 8 ≠ table + 24)
    (orderPos' : order + count * 8 ≠ orderPos + index * 8) :
    ∃ post, evaluateHOLFiniteState state hashInsertValueTail = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      post.memory (order + count * 8) = .word index ∧ post.memory (orderPos + index * 8) = .word count ∧
      ∀ q : BitVec 64, q.toNat < capacity.toNat → q ≠ index → hashOccupancyRead post used q = hashOccupancyRead state used q := by
  have d40 : state.memaddrs (table + 40#64) := ready.valuesDomain
  have c40 : state.memory (table + 40#64) = .word values := ready.valuesMemory
  have address : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) hashSetValueAddress =
      some (.val (.word (values + index * 8))) := by
    simp [hashSetValueAddress,evalHOLExact,evalListHOLExact,hashLocalAddress,ready.tableLocal,ready.indexLocal,wordOpHOL,
      wordOp,panOpHOL,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,d40,c40]
  have store := evaluate_store_word state (values + index * 8) value hashSetValueAddress (.var .local (ofString "value"))
    address ready.valueLocal ready.valueDomain
  have literalSeparate : panByteAlignHOL (used + index) ≠ values + index * 8#64 := ready.valueSeparate index ready.inside
  have literalCountSeparate : table + 24#64 ≠ values + index * 8#64 := ready.valueCountSeparate
  have byteAfter : (sourceWriteWord state (values + index * 8) value).memory (panByteAlignHOL (used + index)) = .word cell := by
    simpa [sourceWriteWord,literalSeparate] using ready.byteMemory
  have countAfter : (sourceWriteWord state (values + index * 8) value).memory (table + 24) = .word count := by
    simpa [sourceWriteWord,literalCountSeparate] using ready.countMemory
  obtain ⟨post,tail,memory,_,_,_,addresses,endian,_⟩ := evaluate_hashInsert_occupancy_count_memory (sourceWriteWord state (values + index * 8) value)
    used table order orderPos count index cell
    ready.tableLocal ready.orderLocal ready.orderPosLocal ready.usedLocal ready.indexLocal ready.byteDomain byteAfter
    ready.orderDomain ready.orderPosDomain ready.countDomain countAfter (Ne.symm (ready.separate index ready.inside).2.2)
  refine ⟨post,?_,?_,?_,?_⟩
  · unfold hashInsertValueTail
    rw [evaluateHOLFiniteState_seq_line780,store]
    exact tail
  · rw [memory]; simp only [sourceWriteWord]; rw [if_neg countOrder,if_neg orderPos',if_true]
  · rw [memory]; simp only [sourceWriteWord]; rw [if_neg countPos,if_true]
  · intro q inside different
    obtain ⟨s1,s2,s3⟩ := ready.separate q inside
    have marked := occupancyRead_congr_at post
      (sourceWriteByte (sourceWriteWord state (values + index * 8) value) (used + index) 1 cell) used q
      (by rw [memory]; simp only [sourceWriteWord]; rw [if_neg s3,if_neg s2,if_neg s1]) addresses endian
    rw [marked]
    have other : used + q ≠ used + index := by
      intro h; apply different; have := congrArg (fun x => x - used) h; simpa using this
    have loaded := sourceWriteByte_load_other (sourceWriteWord state (values + index * 8) value) (used + index) 1 cell
      (used + q) other byteAfter
    unfold hashOccupancyRead
    rw [show (sourceWriteByte (sourceWriteWord state (values + index * 8) value) (used + index) 1 cell).memaddrs =
      (sourceWriteWord state (values + index * 8) value).memaddrs from rfl,
      show (sourceWriteByte (sourceWriteWord state (values + index * 8) value) (used + index) 1 cell).be =
      (sourceWriteWord state (values + index * 8) value).be from rfl,loaded]
    have valueFar := ready.valueSeparate q inside
    exact occupancyRead_congr_at (sourceWriteWord state (values + index * 8) value) state used q
      (by simp only [sourceWriteWord]; rw [if_neg valueFar]) rfl rfl

#print axioms HashInsertTailReady.run_tables

set_option maxHeartbeats 1000000 in
/-- Insertion also keeps every order and order-position cell in table range. -/
theorem htabInsertRaw_returned_tables {F : Type} (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (table key value keyLength keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (tables : OrderInv state capacity count used order orderPos)
    (room : count.toNat < capacity.toNat) (small : keyLength.toNat ≤ 33806089496)
    (budget : keyLength.toNat / 8 + 8 + 1 +
      (capacity.toNat * (0 + 1) + (keyLength.toNat / 32 + keyLength.toNat / 8 + 11 + 0)) ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_insert_raw) = (some (.returned v),post)) :
    HtabAligned keyLength table keys stride capacity used values order orderPos (count + 1) bits post ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ watched : BitVec 64, (watched.toNat < table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ watched.toNat) →
        post.memory watched = state.memory watched) ∧ OrderInv post capacity (count + 1) used order orderPos := by
  have capPos : 0 < capacity.toNat := by rw [inv.power]; exact Nat.two_pow_pos bits
  have tableFits : table.toNat + 72 < 2 ^ 64 := by have := inv.headerKeys; have := keys.isLt; omega
  have header : ∀ k : Nat, k ≤ 64 → (table + BitVec.ofNat 64 k).toNat = table.toNat + k :=
    fun k hk => word_add_toNat table k (by omega)
  have headerDomain : ∀ k : Nat, k ≤ 64 → k % 8 = 0 → state.memaddrs (table + BitVec.ofNat 64 k) := by
    intro k hk ha
    apply inv.domain
    · rw [header k hk]; have := inv.tableAligned; omega
    · rw [header k hk]; omega
    · rw [header k hk]; have := inv.headerKeys; have := inv.usedBefore; have := inv.keysBefore; have := inv.orderBefore; omega
  rw [source_htabInsertRaw_body] at run
  obtain ⟨v1,i1,e1,r1,m1,a1,b1,c1⟩ := dec_returned_state run
  rw [eval_header_load state _ table 16 capacity tableLocal (by exact headerDomain 16 (by omega) (by omega)) (by exact inv.cell16)] at e1
  cases e1
  have t1 : (setVarHOLFinite (ofString "cap") (.val (.word capacity)) state).locals.lookup (ofString "t") =
      some (.val (.word table)) := by
    simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal]
  obtain ⟨v2,i2,e2,r2,m2,a2,b2,c2⟩ := dec_returned_state r1
  rw [eval_header_load _ _ table 0 keyLength t1 (by exact headerDomain 0 (by omega) (by omega)) (by exact inv.cell0)] at e2
  cases e2
  have t2 := (show (setVarHOLFinite (ofString "klen") (.val (.word keyLength))
      (setVarHOLFinite (ofString "cap") (.val (.word capacity)) state)).locals.lookup (ofString "t") =
      some (.val (.word table)) by
    simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] at t1 ⊢
    exact t1)
  obtain ⟨v3,i3,e3,r3,m3,a3,b3,c3⟩ := dec_returned_state r2
  rw [eval_header_load _ _ table 8 stride t2 (by exact headerDomain 8 (by omega) (by omega)) (by exact inv.cell8)] at e3
  cases e3
  obtain ⟨v4,i4,e4,r4,m4,a4,b4,c4⟩ := dec_returned_state r3
  rw [eval_header_load _ _ table 32 keys
    (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] at t2 ⊢
        exact t2)
    (by exact headerDomain 32 (by omega) (by omega)) (by exact inv.cell32)] at e4
  cases e4
  obtain ⟨v5,i5,e5,r5,m5,a5,b5,c5⟩ := dec_returned_state r4
  rw [eval_header_load _ _ table 48 used
    (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] at t2 ⊢
        exact t2)
    (by exact headerDomain 48 (by omega) (by omega)) (by exact inv.cell48)] at e5
  cases e5
  obtain ⟨v6,i6,e6,r6,m6,a6,b6,c6⟩ := dec_returned_state r5
  rw [eval_header_load _ _ table 56 order
    (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] at t2 ⊢
        exact t2)
    (by exact headerDomain 56 (by omega) (by omega)) (by exact inv.cell56)] at e6
  cases e6
  obtain ⟨v7,i7,e7,r7,m7,a7,b7,c7⟩ := dec_returned_state r6
  rw [eval_header_load _ _ table 64 orderPos
    (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] at t2 ⊢
        exact t2)
    (by exact headerDomain 64 (by omega) (by omega)) (by exact inv.cell64)] at e7
  cases e7
  generalize hs7 : setVarHOLFinite (ofString "order_pos") (.val (.word orderPos)) (setVarHOLFinite (ofString "order") (.val (.word order))
    (setVarHOLFinite (ofString "used") (.val (.word used)) (setVarHOLFinite (ofString "keys") (.val (.word keys))
      (setVarHOLFinite (ofString "stride") (.val (.word stride)) (setVarHOLFinite (ofString "klen") (.val (.word keyLength))
        (setVarHOLFinite (ofString "cap") (.val (.word capacity)) state)))))) = s7 at r7
  have s7Locals : InsertLocals s7 table key value capacity keyLength stride keys used order orderPos := by
    rw [← hs7]
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
      simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal,keyLocal,valueLocal] 
  have s7Facts : s7.memory = state.memory ∧ s7.memaddrs = state.memaddrs ∧ s7.be = state.be ∧ s7.code = state.code ∧
      s7.clock = state.clock := by
    rw [← hs7]; exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  obtain ⟨tL,kL,vL,capL,lenL,strideL,keysL,usedL,orderL,orderPosL⟩ := s7Locals
  obtain ⟨values',body,callee,returnShape,w,bodyPost,resumed,inner,args,lookup,bodyRun,rm,ra,rb,rc,rclk,rh,ragree,
    rrun,im,ia,ib,ic⟩ := decCall_returned_body r7
  have argsExact : evalListHOLFinite s7 (h := fun a => Classical.propDecidable (s7.memaddrs a))
      [.var .local (ofString "key"),.var .local (ofString "klen")] = some [.val (.word key),.val (.word keyLength)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,kL,lenL]
  rw [argsExact] at args
  cases args
  have installed : s7.code.lookup (ofString "htab_hash") =
      some ([(ofString "p",.one),(ofString "key_len",.one)],sourceFunctionBody Guest.guestFn_htab_hash,.one) := by
    rw [s7Facts.2.2.2.1,inv.code]; exact originalRuntimeCode_hash_lookup
  rw [pan_two_word_lookup s7.code.lookup (ofString "htab_hash") (ofString "p") (ofString "key_len")
    (sourceFunctionBody Guest.guestFn_htab_hash) key keyLength (by decide) installed] at lookup
  cases lookup
  generalize hentry : callEntryStateHOLFinite s7 ((HolFiniteMapExact.empty.update (ofString "p",.val (.word key))).update
    (ofString "key_len",.val (.word keyLength))) = entry at bodyRun rclk
  have entryFacts : entry.memory = state.memory ∧ entry.memaddrs = state.memaddrs ∧ entry.be = state.be ∧
      entry.code = state.code ∧ entry.clock = state.clock - 1 := by
    rw [← hentry]; exact ⟨s7Facts.1,s7Facts.2.1,s7Facts.2.2.1,s7Facts.2.2.2.1,by rw [← s7Facts.2.2.2.2]; rfl⟩
  have hashBound := evaluate_htabHash_body_bounded entry (entryFacts.2.2.2.1.trans inv.code) keyLength
    (by rw [← hentry]; simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) (by omega)
    (by rw [entryFacts.2.2.2.2]; omega)
  unfold RunBounded at hashBound
  rw [bodyRun] at hashBound
  obtain ⟨hb1,hb2,_⟩ := hashBound
  dsimp only at hb1 hb2
  have hashMemory := evaluate_readOnly_memory _ htabHash_readOnly entry
  have hashMeta := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_htab_hash)
  rw [bodyRun] at hashMemory hashMeta
  have resumedFacts : resumed.memory = state.memory ∧ resumed.memaddrs = state.memaddrs ∧ resumed.be = state.be ∧
      resumed.code = state.code ∧ state.clock ≤ resumed.clock + (keyLength.toNat / 8 + 8 + 1) := by
    refine ⟨rm.trans (hashMemory.trans entryFacts.1),ra.trans (hashMeta.2.1.trans entryFacts.2.1),
      rb.trans (hashMeta.2.2.1.trans entryFacts.2.2.1),rc.trans (hashMeta.1.trans entryFacts.2.2.2.1),?_⟩
    have := rclk hb2
    have := entryFacts.2.2.2.2
    omega
  have resumedLocals : InsertLocals resumed table key value capacity keyLength stride keys used order orderPos := by
    apply InsertLocals.transfer (s := s7) ⟨tL,kL,vL,capL,lenL,strideL,keysL,usedL,orderL,orderPosL⟩
    intro k member
    apply ragree
    intro e
    subst e
    revert member
    decide
  obtain ⟨tR,kR,vR,capR,lenR,strideR,keysR,usedR,orderR,orderPosR⟩ := resumedLocals
  obtain ⟨indexValue,i8,e8,r8,m8,a8,b8,c8⟩ := dec_returned_state rrun
  obtain ⟨start,rfl,startInside⟩ := eval_hashFind_index_range resumed capacity bits inv.power capR indexValue e8
  generalize he : setVarHOLFinite (ofString "i") (.val (.word start)) resumed = e at r8
  have eLocals : InsertLocals e table key value capacity keyLength stride keys used order orderPos := by
    rw [← he]; exact InsertLocals.setVar ⟨tR,kR,vR,capR,lenR,strideR,keysR,usedR,orderR,orderPosR⟩ _ _ (by decide)
  have eIndex : e.locals.lookup (ofString "i") = some (.val (.word start)) := by
    rw [← he]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have eFacts : e.memory = state.memory ∧ e.memaddrs = state.memaddrs ∧ e.be = state.be ∧ e.code = state.code ∧
      e.clock = resumed.clock := by
    rw [← he]; exact ⟨resumedFacts.1,resumedFacts.2.1,resumedFacts.2.2.1,resumedFacts.2.2.2.1,rfl⟩
  have readSame : ∀ {G : Type} (r : PanSemStateFiniteExact 64 G), r.memory = state.memory → r.memaddrs = state.memaddrs →
      r.be = state.be → ∀ slot, hashOccupancyRead r used slot = hashOccupancyRead state used slot := by
    intro G r hm ha hb slot
    unfold hashOccupancyRead
    rw [hm,ha,hb]
  obtain ⟨empty,emptyInside,emptyRead⟩ := hashOccupiedCount_exists_empty capacity (hashOccupancyRead state used)
    (by rw [← inv.agreement]; exact room)
  obtain ⟨tE,kE,vE,capE,lenE,strideE,keysE,usedE,orderE,orderPosE⟩ := eLocals
  rw [evaluateHOLFiniteState_seq_line780] at r8
  have loopBound := hashInsertLoop_run capacity used empty keyLength bits inv.power emptyInside capacity.toNat e
    (eFacts.2.2.2.1.trans inv.code)
    ⟨capE,usedE,lenE,⟨keys,keysE⟩,⟨stride,strideE⟩,⟨key,kE⟩,
      by have := readSame e eFacts.1 eFacts.2.1 eFacts.2.2.1 empty; unfold hashOccupancyRead at this emptyRead; rw [this]; exact emptyRead,
      start,eIndex,startInside,Nat.le_of_lt (hashProbeDistance_lt_capacity _ _ _ startInside emptyInside)⟩
    (by rw [eFacts.2.2.2.2]; have := resumedFacts.2.2.2.2; omega)
  cases loopRun : evaluateHOLFiniteState e (.while (hashProbeOccupied (ofString "i")) (hashProbeStep (ofString "i"))) with
  | mk loopResult m =>
    rw [loopRun] at r8 loopBound
    obtain ⟨lb1,_,_,_⟩ := loopBound
    dsimp only at lb1
    cases loopResult with
    | some r =>
      exfalso
      simp only at r8
      obtain ⟨er,_⟩ := Prod.mk.inj r8
      simp only [Option.some.injEq] at er
      subst er
      exact while_returned_invariant (hashProbeOccupied (ofString "i")) (hashProbeStep (ofString "i"))
        (fun _ => True) (fun _ => False) (fun _ _ => trivial)
        (fun s v post _ run => absurd (congrArg Prod.fst run) (hashProbeStep_not_returned s _ v))
        (fun _ _ _ _ => trivial) e.clock e rfl trivial v m loopRun
    | none =>
      simp only at r8
      have exit := while_normal_exit (hashProbeOccupied (ofString "i")) (hashProbeStep (ofString "i"))
        (fun {G} (s : PanSemStateFiniteExact 64 G) => s.memory = state.memory ∧ s.memaddrs = state.memaddrs ∧
          s.be = state.be ∧ s.code = state.code ∧
          InsertLocals s table key value capacity keyLength stride keys used order orderPos ∧
          ∃ index : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word index)) ∧ index.toNat < capacity.toNat)
        (fun s h => h)
        (by
          intro G s post ⟨sm,sa,sb,sc,sl,index,iL,inside⟩ flow
          have stepRun := evaluate_hashProbeStep s (ofString "i") index capacity iL sl.2.2.2.1
          rcases flow with normal | cont
          · rw [stepRun] at normal
            cases normal
            refine ⟨sm,sa,sb,sc,InsertLocals.setVar sl _ _ (by decide),hashProbeNext index capacity,
              by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],?_⟩
            rw [hashProbeNext_toNat index capacity bits inv.power inside]
            exact Nat.mod_lt _ capPos
          · rw [stepRun] at cont; cases cont)
        (fun s => hashProbeStep_not_break s _)
        e.clock e rfl ⟨eFacts.1,eFacts.2.1,eFacts.2.2.1,eFacts.2.2.2.1,⟨tE,kE,vE,capE,lenE,strideE,keysE,usedE,orderE,orderPosE⟩,
          start,eIndex,startInside⟩ m loopRun
      obtain ⟨⟨mm,ma,mb,mc,mLocals,slot,slotL,slotInside⟩,mZero⟩ := exit
      have slotEmpty : hashOccupancyRead state used slot = some 0 := by
        rw [← readSame m mm ma mb slot]
        exact hashProbeOccupied_zero_read m slot used slotL mLocals.2.2.2.2.2.2.2.1 mZero
      obtain ⟨tM,kM,vM,capM,lenM,strideM,keysM,usedM,orderM,orderPosM⟩ := mLocals
      -- layout arithmetic
      have kb := inv.keysBefore
      have vb := inv.valuesBefore
      have ub := inv.usedBefore
      have ob := inv.orderBefore
      have eb := inv.endBound
      have hk := inv.headerKeys
      have hv := inv.headerValues
      have fitsK := inv.fits
      have slotStride : slot.toNat * stride.toNat + stride.toNat ≤ capacity.toNat * stride.toNat := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ slotInside
      have dstNat : (keys + slot * stride).toNat = keys.toNat + slot.toNat * stride.toNat :=
        word_mul_add_toNat keys slot stride (by omega)
      have dstAligned : (keys + slot * stride).toNat % 8 = 0 := by
        rw [dstNat]
        have : slot.toNat * stride.toNat % 8 = 0 := by rw [Nat.mul_mod,inv.strideAligned]; simp
        have := inv.keysAligned
        omega
      have eight : (8 : BitVec 64).toNat = 8 := rfl
      have valueNat : (values + slot * 8).toNat = values.toNat + slot.toNat * 8 := by
        rw [word_mul_add_toNat values slot 8 (by rw [eight]; omega),eight]
      have orderNat : (order + count * 8).toNat = order.toNat + count.toNat * 8 := by
        rw [word_mul_add_toNat order count 8 (by rw [eight]; omega),eight]
      have orderPosNat : (orderPos + slot * 8).toNat = orderPos.toNat + slot.toNat * 8 := by
        rw [word_mul_add_toNat orderPos slot 8 (by rw [eight]; omega),eight]
      have byteNat : ∀ s' : BitVec 64, s'.toNat < capacity.toNat →
          (panByteAlignHOL (used + s')).toNat = (used.toNat + s'.toNat) / 8 * 8 := by
        intro s' inside'
        rw [byteAlign_toNat,BitVec.toNat_add_of_lt (by omega)]
      have byteRange : ∀ s' : BitVec 64, s'.toNat < capacity.toNat →
          used.toNat ≤ (panByteAlignHOL (used + s')).toNat ∧ (panByteAlignHOL (used + s')).toNat < used.toNat + capacity.toNat := by
        intro s' inside'
        rw [byteNat s' inside']
        have := inv.usedAligned
        omega
      -- the copy call
      have copyArgs := eval_hashFind_comparison_args_exact m slot keys stride key keyLength slotL keysM strideM kM lenM
      rw [evaluateHOLFiniteState_seq_line780] at r8
      cases copyRun : evaluateHOLFiniteState m (.call (some (none,none)) (ofString "memcpy")
          [hashFindComparisonAddress,.var .local (ofString "key"),.var .local (ofString "klen")]) with
      | mk copyResult c =>
        rw [copyRun] at r8
        cases copyResult with
        | some r =>
          exfalso
          simp only at r8
          obtain ⟨er,_⟩ := Prod.mk.inj r8
          simp only [Option.some.injEq] at er
          subst er
          exact discard_call_not_returned m _ _ v (by rw [copyRun])
        | none =>
          simp only at r8
          have mClock : keyLength.toNat / 32 + keyLength.toNat / 8 + 11 ≤ m.clock := by
            have := resumedFacts.2.2.2.2
            have := eFacts.2.2.2.2
            omega
          have copyFrame : ∀ watched : BitVec 64,
              (watched.toNat < (keys + slot * stride).toNat ∨ (keys + slot * stride).toNat + keyLength.toNat ≤ watched.toNat) →
              c.memory watched = state.memory watched := by
            intro watched outside
            have separated := memcpy_interval_separate (keys + slot * stride) keyLength watched dstAligned
              (by rw [dstNat]; omega) outside
            rw [memcpy_call_normal_memory m c _ (keys + slot * stride) key keyLength watched copyArgs
              (mc.trans inv.code) (fun o ho => (separated o ho).1) (fun o ho => (separated o ho).2) small mClock copyRun,mm]
          have copyMeta := evaluateHOLFiniteState_metadata m (.call (some (none,none)) (ofString "memcpy")
            [hashFindComparisonAddress,.var .local (ofString "key"),.var .local (ofString "klen")])
          rw [copyRun] at copyMeta
          have copyLocal : ∀ k : MlS, c.locals.lookup k = m.locals.lookup k := by
            intro k
            have kept := evaluate_avoidsLocal_flowing k (.call (some (none,none)) (ofString "memcpy")
              [hashFindComparisonAddress,.var .local (ofString "key"),.var .local (ofString "klen")]) (by simp [avoidsLocal]) m
              (by rw [copyRun]; exact Or.inl rfl)
            rw [copyRun] at kept
            exact kept
          have h24 : (table + 24 : BitVec 64).toNat = table.toNat + 24 := header 24 (by omega)
          have h40 : (table + 40 : BitVec 64).toNat = table.toNat + 40 := header 40 (by omega)
          have cAddr : c.memaddrs = state.memaddrs := copyMeta.2.1.trans ma
          have cBe : c.be = state.be := copyMeta.2.2.1.trans mb
          have cDomain : ∀ address : BitVec 64, address.toNat % 8 = 0 → table.toNat ≤ address.toNat →
              address.toNat < orderPos.toNat + capacity.toNat * 8 → c.memaddrs address := by
            intro address a1 a2 a3; rw [cAddr]; exact inv.domain address a1 a2 a3
          have headerMem : ∀ k : Nat, k ≤ 64 → c.memory (table + BitVec.ofNat 64 k) = state.memory (table + BitVec.ofNat 64 k) := by
            intro k hk'
            apply copyFrame
            left; rw [header k hk',dstNat]; omega
          have byteMem : ∀ s' : BitVec 64, s'.toNat < capacity.toNat →
              c.memory (panByteAlignHOL (used + s')) = state.memory (panByteAlignHOL (used + s')) := by
            intro s' inside'
            apply copyFrame
            right; rw [dstNat]; have := byteRange s' inside'; omega
          have cRead : ∀ s' : BitVec 64, s'.toNat < capacity.toNat → hashOccupancyRead c used s' = hashOccupancyRead state used s' :=
            fun s' inside' => occupancyRead_congr_at c state used s' (byteMem s' inside') cAddr cBe
          obtain ⟨cell,hcell⟩ : ∃ cell : BitVec 64, c.memory (panByteAlignHOL (used + slot)) = .word cell := by
            cases h : c.memory (panByteAlignHOL (used + slot)) with
            | word x => exact ⟨x,rfl⟩
          have ready : HashInsertTailReady capacity used table values value order orderPos count slot cell c := {
            tableLocal := (copyLocal _).trans tM
            orderLocal := (copyLocal _).trans orderM
            orderPosLocal := (copyLocal _).trans orderPosM
            usedLocal := (copyLocal _).trans usedM
            indexLocal := (copyLocal _).trans slotL
            valueLocal := (copyLocal _).trans vM
            inside := slotInside
            valuesDomain := cDomain _ (by rw [h40]; have := inv.tableAligned; omega)
              (by rw [h40]; omega) (by rw [h40]; omega)
            valuesMemory := (headerMem 40 (by omega)).trans inv.cell40
            valueDomain := cDomain _ (by rw [valueNat]; have := inv.valuesAligned; omega) (by rw [valueNat]; omega)
              (by rw [valueNat]; omega)
            byteDomain := cDomain _ (by rw [byteNat slot slotInside]; omega)
              (by have := byteRange slot slotInside; omega) (by have := byteRange slot slotInside; omega)
            byteMemory := hcell
            empty := (cRead slot slotInside).trans slotEmpty
            orderDomain := cDomain _ (by rw [orderNat]; have := inv.orderAligned; omega) (by rw [orderNat]; omega)
              (by rw [orderNat]; omega)
            orderPosDomain := cDomain _ (by rw [orderPosNat]; have := inv.orderPosAligned; omega) (by rw [orderPosNat]; omega)
              (by rw [orderPosNat]; omega)
            countDomain := cDomain _ (by rw [h24]; have := inv.tableAligned; omega)
              (by rw [h24]; omega) (by rw [h24]; omega)
            countMemory := (headerMem 24 (by omega)).trans inv.cell24
            agreement := by
              rw [inv.agreement]
              exact hashOccupiedCount_congr capacity _ _ (fun s' inside' => (cRead s' inside').symm)
            noWrap := by have := count.isLt; omega
            valueCountSeparate := word_ne_of_toNat (by rw [h24,valueNat]; omega)
            valueSeparate := fun s' inside' => word_ne_of_toNat (by rw [valueNat]; have := byteRange s' inside'; omega)
            separate := fun s' inside' => ⟨word_ne_of_toNat (by rw [orderNat]; have := byteRange s' inside'; omega),
              word_ne_of_toNat (by rw [orderPosNat]; have := byteRange s' inside'; omega),
              word_ne_of_toNat (by rw [h24]; have := byteRange s' inside'; omega)⟩ }
          obtain ⟨tailPost,tailRun,p24,pAgree,_,_,pCode,pAddr,pBe,pFrame⟩ := ready.run_memory
          obtain ⟨tablesPost,tablesRun,orderWritten,posWritten,readsKept⟩ := ready.run_tables
            (word_ne_of_toNat (by rw [orderNat,h24]; omega)) (word_ne_of_toNat (by rw [orderPosNat,h24]; omega))
            (word_ne_of_toNat (by rw [orderNat,orderPosNat]; omega))
          have sameTail : tailPost = tablesPost := congrArg Prod.snd (tailRun.symm.trans tablesRun)
          subst sameTail
          rw [htabInsertRawFinish_eq,tailRun] at r8
          obtain ⟨_,hp⟩ := Prod.mk.inj r8
          subst hp
          have postMem : post.memory = tailPost.memory :=
            m1.trans (m2.trans (m3.trans (m4.trans (m5.trans (m6.trans (m7.trans (im.trans m8)))))))
          have postAddr : post.memaddrs = state.memaddrs :=
            (a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans (a7.trans (ia.trans a8)))))))).trans (pAddr.trans cAddr)
          have postBe : post.be = state.be :=
            (b1.trans (b2.trans (b3.trans (b4.trans (b5.trans (b6.trans (b7.trans (ib.trans b8)))))))).trans (pBe.trans cBe)
          have postCode : post.code = originalRuntimeCode :=
            (c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (ic.trans c8)))))))).trans
              (pCode.trans (copyMeta.1.trans (mc.trans inv.code)))
          have untouched : ∀ watched : BitVec 64, watched ≠ values + slot * 8 → watched ≠ panByteAlignHOL (used + slot) →
              watched ≠ order + count * 8 → watched ≠ orderPos + slot * 8 → watched ≠ table + 24 →
              (watched.toNat < (keys + slot * stride).toNat ∨ (keys + slot * stride).toNat + keyLength.toNat ≤ watched.toNat) →
              post.memory watched = state.memory watched := by
            intro watched n1 n2 n3 n4 n5 outside
            rw [postMem,pFrame watched n1 n2 n3 n4 n5,copyFrame watched outside]
          have byteSlot := byteRange slot slotInside
          have cellKeep : ∀ k : Nat, k ≤ 64 → k ≠ 24 → post.memory (table + BitVec.ofNat 64 k) = state.memory (table + BitVec.ofNat 64 k) := by
            intro k hk' ne24
            apply untouched
            · exact word_ne_of_toNat (by rw [header k hk',valueNat]; omega)
            · exact word_ne_of_toNat (by rw [header k hk']; omega)
            · exact word_ne_of_toNat (by rw [header k hk',orderNat]; omega)
            · exact word_ne_of_toNat (by rw [header k hk',orderPosNat]; omega)
            · exact word_ne_of_toNat (by rw [header k hk',h24]; omega)
            · left; rw [header k hk',dstNat]; omega
          refine ⟨{
            code := postCode
            power := inv.power
            tableAligned := inv.tableAligned
            keysAligned := inv.keysAligned
            strideAligned := inv.strideAligned
            valuesAligned := inv.valuesAligned
            usedAligned := inv.usedAligned
            orderAligned := inv.orderAligned
            orderPosAligned := inv.orderPosAligned
            headerKeys := inv.headerKeys
            headerValues := inv.headerValues
            keysBefore := inv.keysBefore
            valuesBefore := inv.valuesBefore
            usedBefore := inv.usedBefore
            orderBefore := inv.orderBefore
            endBound := inv.endBound
            fits := inv.fits
            domain := fun address a1' a2' a3' => by rw [postAddr]; exact inv.domain address a1' a2' a3'
            cell0 := (cellKeep 0 (by omega) (by omega)).trans inv.cell0
            cell8 := (cellKeep 8 (by omega) (by omega)).trans inv.cell8
            cell16 := (cellKeep 16 (by omega) (by omega)).trans inv.cell16
            cell24 := by rw [postMem]; exact p24
            cell32 := (cellKeep 32 (by omega) (by omega)).trans inv.cell32
            cell40 := (cellKeep 40 (by omega) (by omega)).trans inv.cell40
            cell48 := (cellKeep 48 (by omega) (by omega)).trans inv.cell48
            cell56 := (cellKeep 56 (by omega) (by omega)).trans inv.cell56
            cell64 := (cellKeep 64 (by omega) (by omega)).trans inv.cell64
            agreement := by
              rw [pAgree]
              apply hashOccupiedCount_congr
              intro s' _
              exact (occupancyRead_congr_at post tailPost used s' (by rw [postMem])
                (postAddr.trans (pAddr.trans cAddr).symm) (postBe.trans (pBe.trans cBe).symm)).symm },
            postAddr,postBe,?_,?_⟩
          intro watched outside
          apply untouched
          · exact word_ne_of_toNat (by rw [valueNat]; omega)
          · exact word_ne_of_toNat (by omega)
          · exact word_ne_of_toNat (by rw [orderNat]; omega)
          · exact word_ne_of_toNat (by rw [orderPosNat]; omega)
          · exact word_ne_of_toNat (by rw [h24]; omega)
          · rw [dstNat]; omega
          have kq := inv.keysBefore; have vq := inv.valuesBefore; have uq := inv.usedBefore; have oq := inv.orderBefore
          have countNat : (count + 1).toNat = count.toNat + 1 := by
            rw [BitVec.toNat_add_of_lt (by have := capacity.isLt; change count.toNat + 1 < 2 ^ 64; omega)]; rfl
          constructor
          · intro q inside occupied
            by_cases same : q = slot
            · subst same
              exact ⟨count,by rw [postMem]; exact posWritten,room⟩
            · have qN := inv.slot_toNat q inside
              have ne : orderPos + q * 8 ≠ orderPos + slot * 8 := by
                apply word_ne_of_toNat
                rw [qN.2.2.1,orderPosNat]
                intro h
                apply same
                apply BitVec.eq_of_toNat_eq
                omega
              have postRead : hashOccupancyRead post used q = hashOccupancyRead state used q := by
                rw [occupancyRead_congr_at post tailPost used q (by rw [postMem])
                  (postAddr.trans (pAddr.trans cAddr).symm) (postBe.trans (pBe.trans cBe).symm),
                  readsKept q inside same,cRead q inside]
              obtain ⟨y,hy,ylt⟩ := tables.1 q inside (by rw [← postRead]; exact occupied)
              refine ⟨y,?_,ylt⟩
              rw [untouched (orderPos + q * 8) (word_ne_of_toNat (by rw [qN.2.2.1,valueNat]; omega))
                (word_ne_of_toNat (by rw [qN.2.2.1]; omega))
                (word_ne_of_toNat (by rw [qN.2.2.1,orderNat]; omega)) ne
                (word_ne_of_toNat (by rw [qN.2.2.1,h24]; omega)) (Or.inr (by rw [qN.2.2.1,dstNat]; omega))]
              exact hy
          · intro k inside
            rw [countNat] at inside
            by_cases same : k = count
            · subst same
              exact ⟨slot,by rw [postMem]; exact orderWritten,slotInside⟩
            · have kLt : k.toNat < count.toNat := by
                have : k.toNat ≠ count.toNat := fun h => same (BitVec.eq_of_toNat_eq h)
                omega
              have kN := inv.slot_toNat k (by omega)
              have ne : order + k * 8 ≠ order + count * 8 := by
                apply word_ne_of_toNat
                rw [kN.2.1,orderNat]
                omega
              obtain ⟨x,hx,xlt⟩ := tables.2 k kLt
              refine ⟨x,?_,xlt⟩
              rw [untouched (order + k * 8) (word_ne_of_toNat (by rw [kN.2.1,valueNat]; omega))
                (word_ne_of_toNat (by rw [kN.2.1]; omega)) ne
                (word_ne_of_toNat (by rw [kN.2.1,orderPosNat]; omega))
                (word_ne_of_toNat (by rw [kN.2.1,h24]; omega)) (Or.inr (by rw [kN.2.1,dstNat]; omega))]
              exact hx

#print axioms htabInsertRaw_returned_tables

theorem OrderInv.transfer {F G : Type} {s : PanSemStateFiniteExact 64 F} {r : PanSemStateFiniteExact 64 G}
    {capacity count used order orderPos : BitVec 64} (o : OrderInv s capacity count used order orderPos)
    (memory : r.memory = s.memory) (addresses : r.memaddrs = s.memaddrs) (endian : r.be = s.be) :
    OrderInv r capacity count used order orderPos :=
  ⟨o.1.transfer memory addresses endian,fun k inside => by rw [memory]; exact o.2 k inside⟩

/-- A normally finishing discarded insertion call keeps the order invariant at count + 1. -/
theorem htabInsertRaw_call_normal_tables {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (table key value keyLength keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits state)
    (tables : OrderInv state capacity count used order orderPos)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (room : count.toNat < capacity.toNat) (small : keyLength.toNat ≤ 33806089496)
    (budget : keyLength.toNat / 8 + 8 + 1 +
      (capacity.toNat * (0 + 1) + (keyLength.toNat / 32 + keyLength.toNat / 8 + 11 + 0)) + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_insert_raw")
      [tableArgument,keyArgument,valueArgument]) = (none,post)) :
    OrderInv post capacity (count + 1) used order orderPos := by
  have installed : state.code.lookup (ofString "htab_insert_raw") =
      some ([(ofString "t",.one),(ofString "key",.one),(ofString "value",.one)],
        sourceFunctionBody Guest.guestFn_htab_insert_raw,.one) := by
    rw [inv.code]; exact originalRuntimeCode_hashInsert_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "htab_insert_raw") (ofString "t") (ofString "key")
    (ofString "value") (sourceFunctionBody Guest.guestFn_htab_insert_raw) table key value
    (by decide) (by decide) (by decide) installed
  obtain ⟨v,output,bodyRun,memory,_⟩ := evaluate_discard_normal_body_memory state post (ofString "htab_insert_raw")
    _ _ _ _ .one args lookup run
  generalize hentry : callEntryStateHOLFinite state
    (((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update (ofString "key",.val (.word key))).update
      (ofString "value",.val (.word value))) = entry at bodyRun
  have entryAddr : entry.memaddrs = state.memaddrs := by rw [← hentry]; rfl
  have entryBe : entry.be = state.be := by rw [← hentry]; rfl
  have entryMem : entry.memory = state.memory := by rw [← hentry]; rfl
  have entryInv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits entry :=
    inv.transfer entryMem entryAddr entryBe (by rw [← hentry]; rfl)
  obtain ⟨_,outAddr,outBe,_,outTables⟩ := htabInsertRaw_returned_tables entry output v table key value keyLength keys
    stride capacity used values order orderPos count bits entryInv
    (by rw [← hentry]; simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by rw [← hentry]; simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by rw [← hentry]; simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (tables.transfer entryMem entryAddr entryBe) room small (by rw [← hentry]; change _ ≤ state.clock - 1; omega) bodyRun
  have meta' := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "htab_insert_raw")
    [tableArgument,keyArgument,valueArgument])
  rw [run] at meta'
  exact outTables.transfer memory (meta'.2.1.trans (outAddr.trans entryAddr).symm)
    (meta'.2.2.1.trans (outBe.trans entryBe).symm)

#print axioms htabInsertRaw_call_normal_tables

/-- Rehash-loop rank with the fresh table's order invariant: counter k ≤ nitems with at most `n` items left, the old
arrays and table locals are words, and the fresh table is aligned at count k. -/
def GrowRehashRankT (keyLength table keys stride capacity used values order orderPos items : BitVec 64) (bits : Nat)
    {F : Type} (s : PanSemStateFiniteExact 64 F) (n : Nat) : Prop :=
  ∃ K : BitVec 64, s.locals.lookup (ofString "k") = some (.val (.word K)) ∧ K.toNat ≤ items.toNat ∧
    items.toNat - K.toNat ≤ n ∧
    s.locals.lookup (ofString "nitems") = some (.val (.word items)) ∧
    s.locals.lookup (ofString "t") = some (.val (.word table)) ∧
    (∃ w : BitVec 64, s.locals.lookup (ofString "keys") = some (.val (.word w))) ∧
    (∃ w : BitVec 64, s.locals.lookup (ofString "stride") = some (.val (.word w))) ∧
    (∃ w : BitVec 64, s.locals.lookup (ofString "vals") = some (.val (.word w))) ∧
    (∃ w : BitVec 64, s.locals.lookup (ofString "order") = some (.val (.word w))) ∧
    HtabAligned keyLength table keys stride capacity used values order orderPos K bits s ∧
    OrderInv s capacity K used order orderPos

/-- The actual growth rehash loop, from rank n, spends at most
n * (insertCallCost + 1) ticks in every outcome; each normal iteration inserts
one item into the fresh aligned table. -/
theorem growRehashLoopT_run (keyLength table keys stride capacity used values order orderPos items : BitVec 64)
    (bits : Nat) (fitsIn : items.toNat < capacity.toNat) (capSmall : capacity.toNat < 2 ^ 62)
    (small : keyLength.toNat ≤ 33806089496) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
      GrowRehashRankT keyLength table keys stride capacity used values order orderPos items bits state n →
      n * (insertCallCost keyLength capacity + 1) ≤ state.clock →
      RankedOutcome state (.cmp .less (.var .local (ofString "k")) (.var .local (ofString "nitems")))
        (n * (insertCallCost keyLength capacity + 1))
        (GrowRehashRankT keyLength table keys stride capacity used values order orderPos items bits) False
        (evaluateHOLFiniteState state hashGrowRehashLoop) := by
  refine rankedWhile_run _ hashGrowRehashBody (insertCallCost keyLength capacity)
    (GrowRehashRankT keyLength table keys stride capacity used values order orderPos items bits) False ?_ ?_
  · intro F s ranked v hv
    obtain ⟨K,kL,_,left,nL,_⟩ := ranked
    rw [eval_localBound_less s (ofString "k") (ofString "nitems") .less (Or.inl rfl) K items (by omega) (by omega) kL nL] at hv
    have : ¬ K.toNat < items.toNat := by omega
    simp [this] at hv
    exact hv.symm
  · intro F s n v code' ranked hv nonzero budget'
    obtain ⟨K,kL,kLe,left,nL,tL,⟨ko,keysL⟩,⟨so,strideL⟩,⟨vo,valsL⟩,⟨oo,orderL⟩,inv,tables⟩ := ranked
    rw [eval_localBound_less s (ofString "k") (ofString "nitems") .less (Or.inl rfl) K items (by omega) (by omega) kL nL] at hv
    have lt : K.toNat < items.toNat := by
      by_cases h : K.toNat < items.toNat
      · exact h
      · simp [h] at hv; exact absurd hv.symm nonzero
    have room : K.toNat < capacity.toNat := by omega
    have dInv : HtabAligned keyLength table keys stride capacity used values order orderPos K bits (decClockHOLFinite s) :=
      inv.transfer rfl rfl rfl rfl
    obtain ⟨empty,emptyInside,emptyRead⟩ := hashOccupiedCount_exists_empty capacity (hashOccupancyRead (decClockHOLFinite s) used)
      (by rw [← dInv.agreement]; exact room)
    -- per-entry facts used by both the bound and the rank
    have entryFacts : ∀ iv : ValueHOL 64,
        let e := setVarHOLFinite (ofString "i") iv (decClockHOLFinite s)
        HtabAligned keyLength table keys stride capacity used values order orderPos K bits e ∧
        e.locals.lookup (ofString "t") = some (.val (.word table)) ∧
        e.locals.lookup (ofString "keys") = some (.val (.word ko)) ∧
        e.locals.lookup (ofString "stride") = some (.val (.word so)) ∧
        e.locals.lookup (ofString "vals") = some (.val (.word vo)) ∧
        e.locals.lookup (ofString "i") = some iv ∧
        e.locals.lookup (ofString "k") = some (.val (.word K)) ∧ e.clock = s.clock - 1 := by
      intro iv
      refine ⟨dInv.transfer rfl rfl rfl rfl,?_,?_,?_,?_,?_,?_,rfl⟩ <;>
        simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,decClockHOLFinite,
          tL,keysL,strideL,valsL,kL]
    have bounded : RunBounded (decClockHOLFinite s) hashGrowRehashBody (insertCallCost keyLength capacity) := by
      unfold hashGrowRehashBody
      apply RunBounded.dec
      intro iv _
      obtain ⟨eInv,eT,eKeys,eStride,eVals,eI,_,eClock⟩ := entryFacts iv
      rw [show insertCallCost keyLength capacity = insertCallCost keyLength capacity + 0 from rfl]
      refine RunBounded.seq ?_ (by rw [eClock]; unfold insertCallCost at budget' ⊢; omega) ?_
      · rcases rehash_args_cases _ table ko so vo iv eT eKeys eStride eVals eI with none | ⟨a,y,args⟩
        · unfold RunBounded
          rw [call_args_none _ _ _ _ none]
          exact ⟨Nat.le_add_right _ _,le_refl _,by simp⟩
        · exact runBounded_htabInsertRaw_call _ none _ _ _ table a y capacity keyLength stride keys used empty bits
            eInv.code args (eInv.header_domain 16 (by omega) (by omega)) eInv.cell16
            (eInv.header_domain 0 (by omega) (by omega)) eInv.cell0
            (eInv.header_domain 8 (by omega) (by omega)) eInv.cell8
            (eInv.header_domain 32 (by omega) (by omega)) eInv.cell32
            (eInv.header_domain 48 (by omega) (by omega)) eInv.cell48
            eInv.power emptyInside (by unfold hashOccupancyRead at emptyRead; exact emptyRead) small
            (by rw [eClock]; unfold insertCallCost at budget'; omega)
      · intro next _ nextCode _
        exact RunBounded.ofProg (ProgBounded.straight _ (by decide)) (nextCode.trans eInv.code) (Nat.zero_le _)
    obtain ⟨b1,b2,b3⟩ := bounded
    refine ⟨b1,b2,b3,?_,?_⟩
    · intro flow
      rcases flow with normal | cont
      · cases hrun : evaluateHOLFiniteState (decClockHOLFinite s) hashGrowRehashBody with
        | mk r post =>
          rw [hrun] at normal
          simp only at normal
          subst normal
          dsimp only
          unfold hashGrowRehashBody at hrun
          obtain ⟨iv,inner,_,innerRun,pm,pa,pb,pc,_,plocals,_⟩ := dec_normal_state hrun
          obtain ⟨eInv,eT,eKeys,eStride,eVals,eI,eK,eClock⟩ := entryFacts iv
          rw [evaluateHOLFiniteState_seq_line780] at innerRun
          cases callRun : evaluateHOLFiniteState (setVarHOLFinite (ofString "i") iv (decClockHOLFinite s))
              (.call (some (none,none)) (ofString "htab_insert_raw")
                [.var .local (ofString "t"),
                 .op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "i"),.var .local (ofString "stride")]],
                 .load .one (hashOrderAddress (ofString "vals") (ofString "i"))]) with
          | mk cr mid =>
            rw [callRun] at innerRun
            cases cr with
            | some r => simp at innerRun
            | none =>
              simp only at innerRun
              rcases rehash_args_cases _ table ko so vo iv eT eKeys eStride eVals eI with none | ⟨a,y,args⟩
              · rw [call_args_none _ _ _ _ none] at callRun
                simp at callRun
              · obtain ⟨midInv,midLocals,midAddr,midBe,_⟩ := htabInsertRaw_call_normal_aligned _ mid _ _ _ table a y
                  keyLength keys stride capacity used values order orderPos K bits eInv args room small
                  (by rw [eClock]; unfold insertCallCost at budget'; omega) callRun
                have midTables := htabInsertRaw_call_normal_tables _ mid _ _ _ table a y
                  keyLength keys stride capacity used values order orderPos K bits eInv
                  (tables.transfer rfl rfl rfl) args room small
                  (by rw [eClock]; unfold insertCallCost at budget'; omega) callRun
                have kMid : mid.locals.lookup (ofString "k") = some (.val (.word K)) := by rw [midLocals]; exact eK
                rw [evaluate_increment_local mid (ofString "k") K kMid] at innerRun
                obtain ⟨_,rfl⟩ := Prod.mk.inj innerRun
                have keep : ∀ x, x ≠ ofString "k" → x ≠ ofString "i" → post.locals.lookup x = s.locals.lookup x := by
                  intro x nk ni
                  rw [plocals x ni]
                  simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm nk]
                  rw [midLocals]
                  simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ni]
                  rfl
                have noWrapK : (K + 1).toNat = K.toNat + 1 := by
                  rw [BitVec.toNat_add_of_lt (by have := items.isLt; simp; omega)]; rfl
                refine ⟨n,le_refl _,⟨K + 1,?_,by rw [noWrapK]; omega,by rw [noWrapK]; omega,
                  by rw [keep _ (by decide) (by decide)]; exact nL,
                  by rw [keep _ (by decide) (by decide)]; exact tL,
                  ⟨ko,by rw [keep _ (by decide) (by decide)]; exact keysL⟩,
                  ⟨so,by rw [keep _ (by decide) (by decide)]; exact strideL⟩,
                  ⟨vo,by rw [keep _ (by decide) (by decide)]; exact valsL⟩,
                  ⟨oo,by rw [keep _ (by decide) (by decide)]; exact orderL⟩,
                  midInv.transfer (pm.trans rfl) (pa.trans rfl) (pb.trans rfl) (pc.trans rfl),
                  midTables.transfer (pm.trans rfl) (pa.trans rfl) (pb.trans rfl)⟩,?_⟩
                · rw [plocals _ (by decide)]
                  simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
                · rw [pc]
                  change mid.code = s.code
                  rw [midInv.code,code']
      · exact absurd cont (by
          have := evaluate_noTopContinue hashGrowRehashBody (by decide) (decClockHOLFinite s); exact this)
    · intro brk
      exact absurd brk (by
        have := evaluate_noTopBreak hashGrowRehashBody (by decide) (decClockHOLFinite s); exact this)
#print axioms growRehashLoopT_run

/-- A returned growth tail also leaves the fresh table's order invariant at the original item count. -/
theorem growTail_returned_tables {F : Type} (s r post : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count ncap p0 p1 p2 p3 p4 p5 : BitVec 64) (bits : Nat)
    (v : ValueHOL 64)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits s)
    (tL : s.locals.lookup (ofString "t") = some (.val (.word table)))
    (itemsL : s.locals.lookup (ofString "nitems") = some (.val (.word count)))
    (ncapL : s.locals.lookup (ofString "ncap") = some (.val (.word ncap)))
    (keysL : s.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideL : s.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (valsL : s.locals.lookup (ofString "vals") = some (.val (.word values)))
    (orderL : s.locals.lookup (ofString "order") = some (.val (.word order)))
    (ncapEq : ncap = capacity * 2)
    (A : GrowAllocated s r ncap stride p0 p1 p2 p3 p4 p5)
    (p0Aligned : p0.toNat % 8 = 0) (headerBelow : table.toNat + 72 ≤ p0.toNat) (p0Inside : p0.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → table.toNat ≤ a.toNat → a.toNat < 33806089496 → s.memaddrs a)
    (room : count.toNat < capacity.toNat) (small : keyLength.toNat ≤ 33806089496)
    (budget : ncap.toNat + 1 + count.toNat * (insertCallCost keyLength ncap + 1) ≤ r.clock)
    (run : evaluateHOLFiniteState r (.seq (.call (some (none,none)) (ofString "memzero")
        [.var .local (ofString "nused"),.var .local (ofString "ncap")])
      (htabGrowHeaderStores (.dec (ofString "k") .one (.const 0) (.seq hashGrowRehashLoop (.return (.const 0)))))) =
        (some (.returned v),post)) :
    HtabAligned keyLength table p0 stride ncap p2 p1 p3 p4 count (bits + 1) post ∧
      post.memaddrs = s.memaddrs ∧ post.be = s.be ∧ OrderInv post ncap count p2 p3 p4 := by
  have capSmall : capacity.toNat ≤ 33806089496 := by have := inv.usedBefore; have := inv.orderBefore; have := inv.endBound; omega
  have ncapNat : ncap.toNat = capacity.toNat * 2 := by
    rw [ncapEq]; exact BitVec.toNat_mul_of_lt (by change capacity.toNat * 2 < 2 ^ 64; omega)
  obtain ⟨l2,a2,_⟩ := alloc_step_layout p2 ncap A.f2 A.r2
  rw [← A.e3] at l2
  have f5 := A.f5
  have rUsed : r.locals.lookup (ofString "nused") = some (.val (.word p2)) := A.nused
  have rNcap : r.locals.lookup (ofString "ncap") = some (.val (.word ncap)) := (A.others _ (by decide)).trans ncapL
  have zeroArgs : evalListHOLFinite r (h := fun a => Classical.propDecidable (r.memaddrs a))
      [.var .local (ofString "nused"),.var .local (ofString "ncap")] = some [.val (.word p2),.val (.word ncap)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,rUsed,rNcap]
  have rCode : r.code = originalRuntimeCode := A.code.trans inv.code
  have p2Aligned : p2.toNat % 8 = 0 := by rw [A.e2]; exact (alloc_step_layout p1 (ncap * 8) A.f1 A.r1).2.1
  obtain ⟨m,zeroRun,_,zc1,_,_,zcode,zaddr,zbe,zlocals,zocc⟩ := evaluate_memzero_aligned_call_cells r _ _ p2 ncap zeroArgs rCode
    (by omega) (by omega) p2Aligned
    (by
      intro offset inside
      rw [A.memaddrs]
      have align := byteAlign_toNat (p2 + BitVec.ofNat 64 offset)
      have sum : (p2 + BitVec.ofNat 64 offset).toNat = p2.toNat + offset := word_add_toNat p2 offset (by omega)
      rw [sum] at align
      have keysB : table.toNat ≤ p2.toNat := by
        have := (alloc_step_layout p0 (ncap * stride) p0Inside A.r0).1
        have := (alloc_step_layout p1 (ncap * 8) A.f1 A.r1).1
        rw [← A.e1] at *; rw [← A.e2] at *; omega
      exact arena _ (by rw [align]; omega) (by rw [align]; omega) (by rw [align]; omega))
  have zeroFrame : ∀ watched : BitVec 64, (watched.toNat < p2.toNat ∨ p2.toNat + ncap.toNat ≤ watched.toNat) →
      m.memory watched = s.memory watched := by
    intro watched outside
    rw [(memzero_call_normal_memory r m _ p2 ncap watched zeroArgs rCode p2Aligned (by omega) outside zeroRun).1,A.memory]
  rw [evaluateHOLFiniteState_seq_line780,zeroRun] at run
  simp only at run
  have mLocal : ∀ k, k ∉ growAllocNames → m.locals.lookup k = s.locals.lookup k := by
    intro k notIn; rw [zlocals]; exact A.others k notIn
  have mT := mLocal _ (by decide) |>.trans tL
  have mNcap : m.locals.lookup (ofString "ncap") = some (.val (.word ncap)) := by rw [zlocals]; exact rNcap
  have mKeys : m.locals.lookup (ofString "nkeys") = some (.val (.word p0)) := by rw [zlocals]; exact A.nkeys
  have mVals : m.locals.lookup (ofString "nvals") = some (.val (.word p1)) := by rw [zlocals]; exact A.nvals
  have mUsed : m.locals.lookup (ofString "nused") = some (.val (.word p2)) := by rw [zlocals]; exact A.nused
  have mOrder : m.locals.lookup (ofString "norder") = some (.val (.word p3)) := by rw [zlocals]; exact A.norder
  have mOrderPos : m.locals.lookup (ofString "norder_pos") = some (.val (.word p4)) := by rw [zlocals]; exact A.norderPos
  have mCode : m.code = originalRuntimeCode := zcode.trans rCode
  unfold htabGrowHeaderStores at run
  have run1 := store_seq_returned m post _ _ (table + 16) ncap (eval_hashLocalAddress m _ table 16 mT)
    (by simp [evalHOLExact,mNcap]) run
  generalize hw1 : sourceWriteWord m (table + 16) ncap = w1 at run1
  have w1L : w1.locals = m.locals := by rw [← hw1]; rfl
  have run2 := store_seq_returned w1 post _ _ (table + 32) p0 (eval_hashLocalAddress w1 _ table 32 (by rw [w1L]; exact mT))
    (by simp [evalHOLExact,w1L,mKeys]) run1
  generalize hw2 : sourceWriteWord w1 (table + 32) p0 = w2 at run2
  have w2L : w2.locals = m.locals := by rw [← hw2]; exact w1L
  have run3 := store_seq_returned w2 post _ _ (table + 40) p1 (eval_hashLocalAddress w2 _ table 40 (by rw [w2L]; exact mT))
    (by simp [evalHOLExact,w2L,mVals]) run2
  generalize hw3 : sourceWriteWord w2 (table + 40) p1 = w3 at run3
  have w3L : w3.locals = m.locals := by rw [← hw3]; exact w2L
  have run4 := store_seq_returned w3 post _ _ (table + 48) p2 (eval_hashLocalAddress w3 _ table 48 (by rw [w3L]; exact mT))
    (by simp [evalHOLExact,w3L,mUsed]) run3
  generalize hw4 : sourceWriteWord w3 (table + 48) p2 = w4 at run4
  have w4L : w4.locals = m.locals := by rw [← hw4]; exact w3L
  have run5 := store_seq_returned w4 post _ _ (table + 56) p3 (eval_hashLocalAddress w4 _ table 56 (by rw [w4L]; exact mT))
    (by simp [evalHOLExact,w4L,mOrder]) run4
  generalize hw5 : sourceWriteWord w4 (table + 56) p3 = w5 at run5
  have w5L : w5.locals = m.locals := by rw [← hw5]; exact w4L
  have run6 := store_seq_returned w5 post _ _ (table + 64) p4 (eval_hashLocalAddress w5 _ table 64 (by rw [w5L]; exact mT))
    (by simp [evalHOLExact,w5L,mOrderPos]) run5
  generalize hw6 : sourceWriteWord w5 (table + 64) p4 = w6 at run6
  have w6L : w6.locals = m.locals := by rw [← hw6]; exact w5L
  have run7 := store_seq_returned w6 post _ _ (table + 24) 0 (eval_hashLocalAddress w6 _ table 24 (by rw [w6L]; exact mT))
    (by simp [evalHOLExact]) run6
  generalize hw7 : sourceWriteWord w6 (table + 24) 0 = w7 at run7
  have w7L : w7.locals = m.locals := by rw [← hw7]; exact w6L
  have step : ∀ (a b : PanSemStateFiniteExact 64 F) (addr val : BitVec 64), sourceWriteWord a addr val = b →
      b.memaddrs = a.memaddrs ∧ b.be = a.be ∧ b.code = a.code ∧ b.clock = a.clock ∧
      ∀ x, b.memory x = if x = addr then .word val else a.memory x := by
    intro a b addr val h; rw [← h]; exact ⟨rfl,rfl,rfl,rfl,fun _ => rfl⟩
  obtain ⟨x1a,x1b,x1c,x1k,x1m⟩ := step _ _ _ _ hw1
  obtain ⟨x2a,x2b,x2c,x2k,x2m⟩ := step _ _ _ _ hw2
  obtain ⟨x3a,x3b,x3c,x3k,x3m⟩ := step _ _ _ _ hw3
  obtain ⟨x4a,x4b,x4c,x4k,x4m⟩ := step _ _ _ _ hw4
  obtain ⟨x5a,x5b,x5c,x5k,x5m⟩ := step _ _ _ _ hw5
  obtain ⟨x6a,x6b,x6c,x6k,x6m⟩ := step _ _ _ _ hw6
  obtain ⟨x7a,x7b,x7c,x7k,x7m⟩ := step _ _ _ _ hw7
  have wFacts : w7.memaddrs = m.memaddrs ∧ w7.be = m.be ∧ w7.code = m.code ∧ w7.clock = m.clock :=
    ⟨x7a.trans (x6a.trans (x5a.trans (x4a.trans (x3a.trans (x2a.trans x1a))))),
     x7b.trans (x6b.trans (x5b.trans (x4b.trans (x3b.trans (x2b.trans x1b))))),
     x7c.trans (x6c.trans (x5c.trans (x4c.trans (x3c.trans (x2c.trans x1c))))),
     x7k.trans (x6k.trans (x5k.trans (x4k.trans (x3k.trans (x2k.trans x1k)))))⟩
  have wMemory : ∀ x : BitVec 64, w7.memory x =
      if x = table + 24 then .word 0 else if x = table + 64 then .word p4 else if x = table + 56 then .word p3 else
      if x = table + 48 then .word p2 else if x = table + 40 then .word p1 else if x = table + 32 then .word p0 else
      if x = table + 16 then .word ncap else m.memory x := by
    intro x; rw [x7m,x6m,x5m,x4m,x3m,x2m,x1m]
  have fresh := grow_fresh_aligned s r m w7 keyLength table keys stride capacity used values order orderPos count ncap
    p0 p1 p2 p3 p4 p5 bits inv ncapEq A p0Aligned headerBelow p0Inside arena zeroFrame zocc (zaddr.trans A.memaddrs)
    (zbe.trans A.be) wMemory wFacts.1 wFacts.2.1 (wFacts.2.2.1.trans mCode)
  -- the counter declaration and the rehash loop
  obtain ⟨kv,inner,ke,innerRun,pm,pa,pb,pc⟩ := dec_returned_state run7
  rw [eval_const_word] at ke
  cases ke
  generalize he : setVarHOLFinite (ofString "k") (.val (.word (0 : BitVec 64))) w7 = e at innerRun
  have eLocal : ∀ k, k ∉ growAllocNames → k ≠ ofString "k" → e.locals.lookup k = s.locals.lookup k := by
    intro k notIn nk
    rw [← he]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm nk]
    rw [w7L]
    exact mLocal k notIn
  have eInv : HtabAligned keyLength table p0 stride ncap p2 p1 p3 p4 0 (bits + 1) e :=
    fresh.transfer (by rw [← he]; rfl) (by rw [← he]; rfl) (by rw [← he]; rfl) (by rw [← he]; rfl)
  have eClock : e.clock = m.clock := by rw [← he]; exact wFacts.2.2.2
  have ranked : GrowRehashRankT keyLength table p0 stride ncap p2 p1 p3 p4 count (bits + 1) e count.toNat :=
    ⟨0,by rw [← he]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],by simp,by simp,
      (eLocal _ (by decide) (by decide)).trans itemsL,(eLocal _ (by decide) (by decide)).trans tL,
      ⟨keys,(eLocal _ (by decide) (by decide)).trans keysL⟩,⟨stride,(eLocal _ (by decide) (by decide)).trans strideL⟩,
      ⟨values,(eLocal _ (by decide) (by decide)).trans valsL⟩,⟨order,(eLocal _ (by decide) (by decide)).trans orderL⟩,
      eInv,OrderInv.of_count_zero eInv⟩
  have loop := growRehashLoopT_run keyLength table p0 stride ncap p2 p1 p3 p4 count (bits + 1) (by omega)
    (by omega) small count.toNat e eInv.code ranked (by rw [eClock]; omega)
  rw [evaluateHOLFiniteState_seq_line780] at innerRun
  cases loopRun : evaluateHOLFiniteState e hashGrowRehashLoop with
  | mk lr L =>
    rw [loopRun] at innerRun loop
    cases lr with
    | some r' =>
      exfalso
      obtain ⟨er,_⟩ := Prod.mk.inj innerRun
      simp only [Option.some.injEq] at er
      subst er
      exact rehashLoop_not_returned e L v loopRun
    | none =>
      simp only at innerRun
      obtain ⟨_,_,_,exitFacts⟩ := loop
      obtain ⟨_,⟨K,kL,kLe,_,nL,_,_,_,_,_,lInv,lTables⟩,_,exitCond⟩ := exitFacts rfl
      have K_eq : K = count := by
        rcases exitCond with zero | f
        · rw [eval_localBound_less L (ofString "k") (ofString "nitems") .less (Or.inl rfl) K count (by omega) (by omega)
            kL nL] at zero
          apply BitVec.eq_of_toNat_eq
          by_cases lt : K.toNat < count.toNat
          · simp [lt] at zero
          · omega
        · exact f.elim
      subst K_eq
      obtain ⟨rm,ra,rb,rc⟩ := return_const_state L inner 0 v innerRun
      have lmeta := evaluateHOLFiniteState_metadata e hashGrowRehashLoop
      rw [loopRun] at lmeta
      have eAddr : e.memaddrs = s.memaddrs := by
        rw [← he]; exact wFacts.1.trans (zaddr.trans A.memaddrs)
      have eBe : e.be = s.be := by rw [← he]; exact wFacts.2.1.trans (zbe.trans A.be)
      refine ⟨lInv.transfer (pm.trans rm) (pa.trans ra) (pb.trans rb) (pc.trans rc),
        (pa.trans ra).trans (lmeta.2.1.trans eAddr),(pb.trans rb).trans (lmeta.2.2.1.trans eBe),
        lTables.transfer (pm.trans rm) (pa.trans ra) (pb.trans rb)⟩

#print axioms growTail_returned_tables

/-- A returned original growth body leaves a doubled aligned table, with its order invariant, at the
same item count (fresh arrays above the old heap pointer), keeping the address
map and endianness. -/
theorem htabGrow_returned_tables {F : Type} (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (keyLength table keys stride capacity used values order orderPos count pointer : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerAligned : pointer.toNat % 8 = 0) (headerBelow : table.toNat + 72 ≤ pointer.toNat)
    (pointerInside : pointer.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → table.toNat ≤ a.toNat → a.toNat < 33806089496 → state.memaddrs a)
    (room : count.toNat < capacity.toNat) (small : keyLength.toNat ≤ 33806089496)
    (budget : growBodyCost keyLength capacity count ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_grow) = (some (.returned v),post)) :
    ∃ keys' used' values' order' orderPos' : BitVec 64,
      HtabAligned keyLength table keys' stride (capacity * 2) used' values' order' orderPos' count (bits + 1) post ∧
        post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ OrderInv post (capacity * 2) count used' order' orderPos' := by
  unfold growBodyCost at budget
  rw [source_htabGrow_body] at run
  obtain ⟨v1,i1,e1,r1,m1,a1,b1,c1⟩ := dec_returned_state run
  rw [eval_header_load state _ table 16 capacity tableLocal (inv.header_domain 16 (by omega) (by omega)) inv.cell16] at e1
  cases e1
  obtain ⟨v2,i2,e2,r2,m2,a2,b2,c2⟩ := dec_returned_state r1
  rw [eval_header_load _ _ table 8 stride
    (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
    (by exact inv.header_domain 8 (by omega) (by omega)) (by exact inv.cell8)] at e2
  cases e2
  obtain ⟨v3,i3,e3,r3,m3,a3,b3,c3⟩ := dec_returned_state r2
  rw [eval_header_load _ _ table 32 keys
    (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
    (by exact inv.header_domain 32 (by omega) (by omega)) (by exact inv.cell32)] at e3
  cases e3
  obtain ⟨v4,i4,e4,r4,m4,a4,b4,c4⟩ := dec_returned_state r3
  rw [eval_header_load _ _ table 40 values
    (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
    (by exact inv.header_domain 40 (by omega) (by omega)) (by exact inv.cell40)] at e4
  cases e4
  obtain ⟨v5,i5,e5,r5,m5,a5,b5,c5⟩ := dec_returned_state r4
  rw [eval_header_load _ _ table 56 order
    (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
    (by exact inv.header_domain 56 (by omega) (by omega)) (by exact inv.cell56)] at e5
  cases e5
  obtain ⟨v6,i6,e6,r6,m6,a6,b6,c6⟩ := dec_returned_state r5
  rw [eval_header_load _ _ table 24 count
    (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
    (by exact inv.header_domain 24 (by omega) (by omega)) (by exact inv.cell24)] at e6
  cases e6
  generalize hs6 : setVarHOLFinite (ofString "nitems") (.val (.word count)) (setVarHOLFinite (ofString "order") (.val (.word order))
    (setVarHOLFinite (ofString "vals") (.val (.word values)) (setVarHOLFinite (ofString "keys") (.val (.word keys))
      (setVarHOLFinite (ofString "stride") (.val (.word stride))
        (setVarHOLFinite (ofString "cap") (.val (.word capacity)) state))))) = s6 at r6
  have s6cap : s6.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    rw [← hs6]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨v7,i7,e7,r7,m7,a7,b7,c7⟩ := dec_returned_state r6
  rw [eval_htabGrow_doubled_capacity s6 capacity s6cap] at e7
  cases e7
  generalize hs7 : setVarHOLFinite (ofString "ncap") (.val (.word (capacity * 2))) s6 = s7 at r7
  have s7Facts : s7.memory = state.memory ∧ s7.memaddrs = state.memaddrs ∧ s7.be = state.be ∧ s7.code = state.code ∧
      s7.clock = state.clock ∧ s7.globals = state.globals := by
    rw [← hs7,← hs6]; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  have lk : ∀ name : MlS, s7.locals.lookup name = (setVarHOLFinite (ofString "ncap") (.val (.word (capacity * 2)))
      (setVarHOLFinite (ofString "nitems") (.val (.word count)) (setVarHOLFinite (ofString "order") (.val (.word order))
        (setVarHOLFinite (ofString "vals") (.val (.word values)) (setVarHOLFinite (ofString "keys") (.val (.word keys))
          (setVarHOLFinite (ofString "stride") (.val (.word stride))
            (setVarHOLFinite (ofString "cap") (.val (.word capacity)) state))))))).locals.lookup name := by
    intro name; rw [← hs7,← hs6]
  have inv7 := inv.transfer s7Facts.1 s7Facts.2.1 s7Facts.2.2.1 s7Facts.2.2.2.1
  obtain ⟨r,inner,p1,p2,p3,p4,p5,A,rClock,tailRun,qm,qa,qb,qc⟩ := growAllocs_returned s7 i7 _ (capacity * 2) stride pointer v
    (by rw [lk]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by rw [lk]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (s7Facts.2.2.2.1.trans inv.code) (by rw [s7Facts.2.2.2.2.2]; exact heap) (by rw [s7Facts.2.2.2.2.1]; omega) r7
  obtain ⟨tailInv,tailAddr,tailBe,tailTables⟩ := growTail_returned_tables s7 r inner keyLength table keys stride capacity used values order
    orderPos count (capacity * 2) pointer p1 p2 p3 p4 p5 bits v inv7
    (by rw [lk]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
    (by rw [lk]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by rw [lk]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by rw [lk]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by rw [lk]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by rw [lk]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by rw [lk]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    rfl A pointerAligned headerBelow pointerInside (fun a h1 h2 h3 => by rw [s7Facts.2.1]; exact arena a h1 h2 h3)
    room small (by rw [s7Facts.2.2.2.2.1] at rClock; omega) tailRun
  have postMem : post.memory = inner.memory := m1.trans (m2.trans (m3.trans (m4.trans (m5.trans (m6.trans (m7.trans qm))))))
  have postAddr : post.memaddrs = inner.memaddrs := a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans (a7.trans qa))))))
  have postBe : post.be = inner.be := b1.trans (b2.trans (b3.trans (b4.trans (b5.trans (b6.trans (b7.trans qb))))))
  have postCode : post.code = inner.code := c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans qc))))))
  exact ⟨pointer,p2,p1,p3,p4,tailInv.transfer postMem postAddr postBe postCode,
    postAddr.trans (tailAddr.trans s7Facts.2.1),postBe.trans (tailBe.trans s7Facts.2.2.1),
    tailTables.transfer postMem postAddr postBe⟩

#print axioms htabGrow_returned_tables

/-- After a normally finishing `htab_grow` call on an aligned table, the table (with its order invariant)
is aligned at doubled capacity with the same count, and the caller's locals,
address map and endianness are unchanged. -/
theorem htabGrow_call_normal_tables {F : Type} (state post : PanSemStateFiniteExact 64 F) (tableArgument : ExpHOL 64)
    (keyLength table keys stride capacity used values order orderPos count pointer : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits state)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [tableArgument] =
      some [.val (.word table)])
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerAligned : pointer.toNat % 8 = 0) (headerBelow : table.toNat + 72 ≤ pointer.toNat)
    (pointerInside : pointer.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → table.toNat ≤ a.toNat → a.toNat < 33806089496 → state.memaddrs a)
    (room : count.toNat < capacity.toNat) (small : keyLength.toNat ≤ 33806089496)
    (budget : growBodyCost keyLength capacity count + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_grow") [tableArgument]) = (none,post)) :
    (∃ keys' used' values' order' orderPos' : BitVec 64,
      HtabAligned keyLength table keys' stride (capacity * 2) used' values' order' orderPos' count (bits + 1) post ∧
      OrderInv post (capacity * 2) count used' order' orderPos') ∧
      post.locals = state.locals ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨v,output,bodyRun,memory,locals⟩ := evaluate_discard_normal_body_memory state post (ofString "htab_grow")
    _ _ _ _ .one args (htabGrow_installed state table inv.code) run
  obtain ⟨k',u',v',o',op',outInv,outAddr,outBe,outTables⟩ := htabGrow_returned_tables
    (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "t",.val (.word table)))) output v keyLength table
    keys stride capacity
    used values order orderPos count pointer bits (inv.transfer rfl rfl rfl rfl)
    (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) (by exact heap)
    pointerAligned headerBelow pointerInside (fun a h1 h2 h3 => by exact arena a h1 h2 h3) room small
    (by change _ ≤ state.clock - 1; omega) bodyRun
  have meta' := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "htab_grow") [tableArgument])
  rw [run] at meta'
  refine ⟨⟨k',u',v',o',op',outInv.transfer memory (meta'.2.1.trans outAddr.symm) (meta'.2.2.1.trans outBe.symm)
    (meta'.1.trans (inv.code.trans outInv.code.symm)),
    outTables.transfer memory (meta'.2.1.trans outAddr.symm) (meta'.2.2.1.trans outBe.symm)⟩,locals,meta'.2.1,meta'.2.2.1⟩

#print axioms htabGrow_call_normal_tables

/-- A word write that misses the occupancy bytes, the order positions and the
live order entries keeps the order invariant. -/
theorem OrderInv.write_far {F : Type} {s : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat}
    (o : OrderInv s capacity count used order orderPos)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits s)
    (address value : BitVec 64)
    (occupancy : ∀ q : BitVec 64, q.toNat < capacity.toNat → address ≠ panByteAlignHOL (used + q))
    (positions : ∀ q : BitVec 64, q.toNat < capacity.toNat → address ≠ orderPos + q * 8)
    (entries : ∀ q : BitVec 64, q.toNat < capacity.toNat → address ≠ order + q * 8) :
    OrderInv (sourceWriteWord s address value) capacity count used order orderPos := by
  have countLe : count.toNat ≤ capacity.toNat := by
    rw [inv.agreement]; unfold hashOccupiedCount; exact (List.countP_le_length).trans (by simp)
  constructor
  · intro q inside occupied
    have read : hashOccupancyRead (sourceWriteWord s address value) used q = hashOccupancyRead s used q :=
      occupancyRead_congr_at _ s used q (by simp only [sourceWriteWord]; rw [if_neg (Ne.symm (occupancy q inside))]) rfl rfl
    obtain ⟨y,hy,ylt⟩ := o.1 q inside (by rw [← read]; exact occupied)
    exact ⟨y,by simp only [sourceWriteWord]; rw [if_neg (Ne.symm (positions q inside))]; exact hy,ylt⟩
  · intro k inside
    obtain ⟨x,hx,xlt⟩ := o.2 k inside
    exact ⟨x,by simp only [sourceWriteWord]; rw [if_neg (Ne.symm (entries k (by omega)))]; exact hx,xlt⟩

#print axioms OrderInv.write_far

/-- A returned original set leaves an aligned table with its order invariant for the same key length and
stride: either the same capacity and count (existing key updated), or count + 1
with load at most one half (key inserted, after growth when needed). -/
theorem htabSet_returned_tables {F : Type} (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (keyLength table keys stride capacity used values order orderPos count key value pointer : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerAligned : pointer.toNat % 8 = 0) (headerBelow : table.toNat + 72 ≤ pointer.toNat)
    (pointerInside : pointer.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → table.toNat ≤ a.toNat → a.toNat < 33806089496 → state.memaddrs a)
    (tables : OrderInv state capacity count used order orderPos)
    (room : count.toNat < capacity.toNat) (small : keyLength.toNat ≤ 33806089496)
    (budget : setBodyCost keyLength capacity count ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set) = (some (.returned v),post)) :
    ∃ (capacity' keys' used' values' order' orderPos' count' : BitVec 64) (bits' : Nat),
      HtabAligned keyLength table keys' stride capacity' used' values' order' orderPos' count' bits' post ∧
      ((capacity' = capacity ∧ count' = count) ∨ (count'.toNat = count.toNat + 1 ∧ count'.toNat * 2 ≤ capacity'.toNat)) ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ OrderInv post capacity' count' used' order' orderPos' := by
  unfold setBodyCost at budget
  have capSmall : capacity.toNat ≤ 33806089496 := by have := inv.usedBefore; have := inv.orderBefore; have := inv.endBound; omega
  rw [source_htabSet_body] at run
  obtain ⟨values0,body,callee,rs,w,bodyPost,r,inner,args,lookup,bodyRun,rm,ra,rb,rc,rg,rclk,rh,ragree,rrun,
    pm,pa,pb,pc⟩ := decCall_returned_globals run
  have argsExact : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,tableLocal,keyLocal]
  rw [argsExact] at args
  cases args
  have installed : state.code.lookup (ofString "htab_find_slot") =
      some ([(ofString "t",.one),(ofString "key",.one)],sourceFunctionBody Guest.guestFn_htab_find_slot,.one) := by
    rw [inv.code]; exact originalRuntimeCode_hashFind_lookup
  rw [pan_two_word_lookup state.code.lookup (ofString "htab_find_slot") (ofString "t") (ofString "key")
    (sourceFunctionBody Guest.guestFn_htab_find_slot) table key (by decide) installed] at lookup
  cases lookup
  generalize hentry : callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update (ofString "key",.val (.word key))) = entry at bodyRun rclk
  have entryFacts : entry.memory = state.memory ∧ entry.memaddrs = state.memaddrs ∧ entry.be = state.be ∧
      entry.code = state.code ∧ entry.globals = state.globals ∧ entry.clock = state.clock - 1 := by
    rw [← hentry]; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  have entryInv := inv.transfer entryFacts.1 entryFacts.2.1 entryFacts.2.2.1 entryFacts.2.2.2.1
  have entryT : entry.locals.lookup (ofString "t") = some (.val (.word table)) := by
    rw [← hentry]; simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨wi,rfl,wiLe⟩ := htabFindSlot_returned_range entry bodyPost table capacity bits entryInv.power entryT
    (entryInv.header_domain 16 (by omega) (by omega)) entryInv.cell16 w bodyRun
  obtain ⟨empty,emptyInside,emptyRead⟩ := hashOccupiedCount_exists_empty capacity (hashOccupancyRead entry used)
    (by rw [← entryInv.agreement]; exact room)
  have findBound := evaluate_htabFindSlot_body_bounded entry entryInv.code table key capacity keyLength stride keys used
    empty bits entryT
    (by rw [← hentry]; simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (entryInv.header_domain 16 (by omega) (by omega)) entryInv.cell16 (entryInv.header_domain 0 (by omega) (by omega))
    entryInv.cell0 (entryInv.header_domain 8 (by omega) (by omega)) entryInv.cell8
    (entryInv.header_domain 32 (by omega) (by omega)) entryInv.cell32 (entryInv.header_domain 48 (by omega) (by omega))
    entryInv.cell48 entryInv.power emptyInside (by unfold hashOccupancyRead at emptyRead; exact emptyRead) small
    (by rw [entryFacts.2.2.2.2.2]; omega)
  unfold RunBounded at findBound
  rw [bodyRun] at findBound
  obtain ⟨fb1,fb2,_⟩ := findBound
  dsimp only at fb1 fb2
  have frame := htabFindSlot_memoryFrame entry entryInv.code
  have meta' := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_htab_find_slot)
  rw [bodyRun] at frame meta'
  have rFacts : r.memory = state.memory ∧ r.memaddrs = state.memaddrs ∧ r.be = state.be ∧ r.code = state.code ∧
      r.globals = state.globals ∧ state.clock ≤ r.clock + (keyLength.toNat / 8 + 8 + 1 +
        (capacity.toNat * (4 * keyLength.toNat + 1 + 0 + 1) + 0)) + 1 :=
    ⟨rm.trans (frame.1.trans entryFacts.1),ra.trans (meta'.2.1.trans entryFacts.2.1),rb.trans (meta'.2.2.1.trans entryFacts.2.2.1),
      rc.trans (meta'.1.trans entryFacts.2.2.2.1),rg.trans (frame.2.trans entryFacts.2.2.2.2.1),
      by rw [rclk fb2]; have := entryFacts.2.2.2.2.2; omega⟩
  have rInv := inv.transfer rFacts.1 rFacts.2.1 rFacts.2.2.1 rFacts.2.2.2.1
  have rTables := tables.transfer rFacts.1 rFacts.2.1 rFacts.2.2.1
  have rT := (ragree _ (by decide)).trans tableLocal
  have rKey := (ragree _ (by decide)).trans keyLocal
  have rValue := (ragree _ (by decide)).trans valueLocal
  rw [evaluateHOLFiniteState_seq_line780] at rrun
  cases upd : evaluateHOLFiniteState r htabSetUpdate with
  | mk ur u =>
    rw [upd] at rrun
    cases ur with
    | some ur =>
      -- existing key: value cell written, then return
      obtain ⟨e,rfl⟩ := Prod.mk.inj rrun
      simp only [Option.some.injEq] at e
      subst e
      obtain ⟨lt,um,ua,ub,uc⟩ := htabSetUpdate_returned r u v table capacity values wi value rT rh rValue wiLe
        (by exact rInv.header_domain 16 (by omega) (by omega)) (by exact rInv.cell16)
        (by exact rInv.header_domain 40 (by omega) (by omega)) (by exact rInv.cell40) upd
      have hv := rInv.headerValues
      have vb := rInv.valuesBefore
      have written := rInv.write_outside (values + wi * 8) value
        (fun k hk => word_ne_of_toNat (by
          rw [word_mul_add_toNat values wi 8 (by change _ + _ * 8 < _; have := used.isLt; omega),
            word_add_toNat table k (by have := keys.isLt; have := rInv.headerKeys; omega)]
          change ¬(_ + _ * 8 = _); omega))
        (fun slot inside => word_ne_of_toNat (by
          rw [word_mul_add_toNat values wi 8 (by change _ + _ * 8 < _; have := used.isLt; omega),byteAlign_toNat,
            BitVec.toNat_add_of_lt (by have := rInv.usedBefore; have := rInv.orderBefore; have := rInv.endBound; omega)]
          have := rInv.usedAligned
          change ¬(_ + _ * 8 = _); omega))
      have writtenTables := rTables.write_far rInv (values + wi * 8) value
        (fun q inside => word_ne_of_toNat (by
          rw [word_mul_add_toNat values wi 8 (by change _ + _ * 8 < _; have := used.isLt; omega),byteAlign_toNat,
            BitVec.toNat_add_of_lt (by have := rInv.usedBefore; have := rInv.orderBefore; have := rInv.endBound; omega)]
          have := rInv.usedAligned
          change ¬(_ + _ * 8 = _); omega))
        (fun q inside => word_ne_of_toNat (by
          rw [word_mul_add_toNat values wi 8 (by change _ + _ * 8 < _; have := used.isLt; omega),
            (rInv.slot_toNat q inside).2.2.1]
          have := rInv.usedBefore; have := rInv.orderBefore
          change ¬(_ + _ * 8 = _); omega))
        (fun q inside => word_ne_of_toNat (by
          rw [word_mul_add_toNat values wi 8 (by change _ + _ * 8 < _; have := used.isLt; omega),
            (rInv.slot_toNat q inside).2.1]
          have := rInv.usedBefore; have := rInv.orderBefore
          change ¬(_ + _ * 8 = _); omega))
      refine ⟨capacity,keys,used,values,order,orderPos,count,bits,
        written.transfer (pm.trans um) (pa.trans ua) (pb.trans ub) (pc.trans uc),Or.inl ⟨rfl,rfl⟩,
        pa.trans (ua.trans rFacts.2.1),pb.trans (ub.trans rFacts.2.2.1),
        writtenTables.transfer (pm.trans um) (pa.trans ua) (pb.trans ub)⟩
    | none =>
      have same := htabSetUpdate_normal r u upd
      subst same
      simp only at rrun
      have capDouble : (capacity * 2).toNat = capacity.toNat * 2 :=
        BitVec.toNat_mul_of_lt (by change capacity.toNat * 2 < 2 ^ 64; omega)
      have countOne : (count + 1).toNat = count.toNat + 1 := by
        rw [BitVec.toNat_add_of_lt (by simp; omega)]; rfl
      have growArgs : evalListHOLFinite u (h := fun a => Classical.propDecidable (u.memaddrs a))
          [.var .local (ofString "t")] = some [.val (.word table)] := by
        rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,rT]
      have insArgs : ∀ g : PanSemStateFiniteExact 64 F, g.locals = u.locals →
          evalListHOLFinite g (h := fun a => Classical.propDecidable (g.memaddrs a))
            [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")] =
            some [.val (.word table),.val (.word key),.val (.word value)] := by
        intro g gl
        rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,gl,rT,rKey,rValue]
      -- the insertion and final return from the state after the growth guard
      have finish : ∀ (g : PanSemStateFiniteExact 64 F) (capacity' keys' used' values' order' orderPos' : BitVec 64)
          (bits' : Nat),
          HtabAligned keyLength table keys' stride capacity' used' values' order' orderPos' count bits' g →
          OrderInv g capacity' count used' order' orderPos' →
          g.locals = u.locals → count.toNat < capacity'.toNat →
          insertCallCost keyLength capacity' ≤ g.clock →
          evaluateHOLFiniteState g (.seq (.call (some (none,none)) (ofString "htab_insert_raw")
            [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")])
            (.return (.const 0))) = (some (.returned v),inner) →
          HtabAligned keyLength table keys' stride capacity' used' values' order' orderPos' (count + 1) bits' inner ∧
            inner.memaddrs = g.memaddrs ∧ inner.be = g.be ∧ OrderInv inner capacity' (count + 1) used' order' orderPos' := by
        intro g capacity' keys' used' values' order' orderPos' bits' gInv gTables gl roomG gClock gRun
        rw [evaluateHOLFiniteState_seq_line780] at gRun
        cases insRun : evaluateHOLFiniteState g (.call (some (none,none)) (ofString "htab_insert_raw")
            [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")]) with
        | mk ir ins =>
          rw [insRun] at gRun
          cases ir with
          | some ir =>
            exfalso
            obtain ⟨e,_⟩ := Prod.mk.inj gRun
            simp only [Option.some.injEq] at e
            subst e
            exact discard_call_not_returned g _ _ v (by rw [insRun])
          | none =>
            simp only at gRun
            obtain ⟨insInv,_,insAddr,insBe,_⟩ := htabInsertRaw_call_normal_aligned g ins _ _ _ table key value keyLength
              keys' stride capacity' used' values' order' orderPos' count bits' gInv (insArgs g gl) roomG small
              (by unfold insertCallCost at gClock; omega) insRun
            have insTables := htabInsertRaw_call_normal_tables g ins _ _ _ table key value keyLength
              keys' stride capacity' used' values' order' orderPos' count bits' gInv gTables (insArgs g gl) roomG small
              (by unfold insertCallCost at gClock; omega) insRun
            obtain ⟨em,ea,eb,ec⟩ := return_const_state ins inner 0 v gRun
            exact ⟨insInv.transfer em ea eb ec,ea.trans insAddr,eb.trans insBe,insTables.transfer em ea eb⟩
      rw [evaluateHOLFiniteState_seq_line780] at rrun
      cases gRun : evaluateHOLFiniteState u (.ite htabSetGuard
          (.call (some (none,none)) (ofString "htab_grow") [.var .local (ofString "t")]) .skip) with
      | mk gr g =>
        rw [gRun] at rrun
        cases gr with
        | some gr =>
          exfalso
          obtain ⟨e,_⟩ := Prod.mk.inj rrun
          simp only [Option.some.injEq] at e
          subst e
          rw [evaluateHOLFiniteState_ite] at gRun
          split at gRun
          · split at gRun
            · simp [evaluateHOLFiniteState_skip] at gRun
            · exact discard_call_not_returned u _ _ v (by rw [gRun])
          · simp at gRun
        | none =>
          simp only at rrun
          have guardVal := eval_htabSetGuard u table capacity count rT (by exact rInv.header_domain 16 (by omega) (by omega))
            (by exact rInv.cell16) (by exact rInv.header_domain 24 (by omega) (by omega)) (by exact rInv.cell24) (by omega)
          rcases ite_normal_cases_cond u g _ _ _ gRun with ⟨gw,gnz,gcond,grown⟩ | ⟨gcond,skipped⟩
          · rw [guardVal] at gcond
            simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at gcond
            have over : capacity.toNat < (count.toNat + 1) * 2 := by
              by_cases h : capacity.toNat < (count.toNat + 1) * 2
              · exact h
              · simp [h] at gcond; exact absurd gcond.symm gnz
            obtain ⟨⟨k',u',v',o',op',gInv,gTables⟩,gLocals,gAddr,gBe⟩ := htabGrow_call_normal_tables u g _ keyLength table keys stride
              capacity used values order orderPos count pointer bits rInv growArgs (by rw [rFacts.2.2.2.2.1]; exact heap)
              pointerAligned headerBelow pointerInside (fun a h1 h2 h3 => by rw [rFacts.2.1]; exact arena a h1 h2 h3) room small
              (by have := rFacts.2.2.2.2.2; omega) grown
            have growB := runBounded_htabGrow_call u _ keyLength table keys stride capacity used values order orderPos count
              pointer bits rInv growArgs (by rw [rFacts.2.2.2.2.1]; exact heap) pointerAligned headerBelow pointerInside
              (fun a h1 h2 h3 => by rw [rFacts.2.1]; exact arena a h1 h2 h3) room small (by have := rFacts.2.2.2.2.2; omega)
            unfold RunBounded at growB
            rw [grown] at growB
            obtain ⟨gb1,_,_⟩ := growB
            dsimp only at gb1
            obtain ⟨fInv,fAddr,fBe,fTables⟩ := finish g (capacity * 2) k' u' v' o' op' (bits + 1) gInv gTables gLocals (by rw [capDouble]; omega)
              (by have := rFacts.2.2.2.2.2; omega) rrun
            refine ⟨capacity * 2,k',u',v',o',op',count + 1,bits + 1,fInv.transfer pm pa pb pc,
              Or.inr ⟨countOne,by rw [countOne,capDouble]; omega⟩,
              pa.trans (fAddr.trans (gAddr.trans rFacts.2.1)),pb.trans (fBe.trans (gBe.trans rFacts.2.2.1)),
              fTables.transfer pm pa pb⟩
          · rw [guardVal] at gcond
            simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at gcond
            have under : ¬ capacity.toNat < (count.toNat + 1) * 2 := by
              intro h; simp [h] at gcond
            rw [evaluateHOLFiniteState_skip] at skipped
            obtain ⟨_,rfl⟩ := Prod.mk.inj skipped
            have mono := insertCallCost_mono keyLength capacity (capacity * 2) (by rw [capDouble]; omega)
            obtain ⟨fInv,fAddr,fBe,fTables⟩ := finish u capacity keys used values order orderPos bits rInv rTables rfl room
              (by have := rFacts.2.2.2.2.2; omega) rrun
            refine ⟨capacity,keys,used,values,order,orderPos,count + 1,bits,fInv.transfer pm pa pb pc,
              Or.inr ⟨countOne,by rw [countOne]; omega⟩,
              pa.trans (fAddr.trans rFacts.2.1),pb.trans (fBe.trans rFacts.2.2.1),fTables.transfer pm pa pb⟩

#print axioms htabSet_returned_tables

/-- After a normally finishing discarded `htab_set` call, the table is aligned (with its order invariant)
for the same key length and stride, with the same count and capacity or with
count + 1 at load at most one half; caller locals, address map and endianness
are unchanged. -/
theorem htabSet_call_normal_tables {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (keyLength table keys stride capacity used values order orderPos count key value pointer : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits state)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerAligned : pointer.toNat % 8 = 0) (headerBelow : table.toNat + 72 ≤ pointer.toNat)
    (pointerInside : pointer.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → table.toNat ≤ a.toNat → a.toNat < 33806089496 → state.memaddrs a)
    (tables : OrderInv state capacity count used order orderPos)
    (room : count.toNat < capacity.toNat) (small : keyLength.toNat ≤ 33806089496)
    (budget : setBodyCost keyLength capacity count + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set")
      [tableArgument,keyArgument,valueArgument]) = (none,post)) :
    (∃ (capacity' keys' used' values' order' orderPos' count' : BitVec 64) (bits' : Nat),
      HtabAligned keyLength table keys' stride capacity' used' values' order' orderPos' count' bits' post ∧
      ((capacity' = capacity ∧ count' = count) ∨ (count'.toNat = count.toNat + 1 ∧ count'.toNat * 2 ≤ capacity'.toNat)) ∧
      OrderInv post capacity' count' used' order' orderPos') ∧
      post.locals = state.locals ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨v,output,bodyRun,memory,locals⟩ := evaluate_discard_normal_body_memory state post (ofString "htab_set")
    _ _ _ _ .one args (htabSet_installed state table key value inv.code) run
  obtain ⟨c',k',u',v',o',op',n',b',outInv,shape,outAddr,outBe,outTables⟩ := htabSet_returned_tables
    (callEntryStateHOLFinite state (((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update
      (ofString "key",.val (.word key))).update (ofString "value",.val (.word value)))) output v keyLength table keys stride
    capacity used values order orderPos count key value pointer bits (inv.transfer rfl rfl rfl rfl)
    (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by exact heap) pointerAligned headerBelow pointerInside (fun a h1 h2 h3 => by exact arena a h1 h2 h3)
    (tables.transfer rfl rfl rfl) room small
    (by change _ ≤ state.clock - 1; omega) bodyRun
  have meta' := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "htab_set")
    [tableArgument,keyArgument,valueArgument])
  rw [run] at meta'
  exact ⟨⟨c',k',u',v',o',op',n',b',outInv.transfer memory (meta'.2.1.trans outAddr.symm) (meta'.2.2.1.trans outBe.symm)
    (meta'.1.trans (inv.code.trans outInv.code.symm)),shape,
    outTables.transfer memory (meta'.2.1.trans outAddr.symm) (meta'.2.2.1.trans outBe.symm)⟩,locals,meta'.2.1,meta'.2.2.1⟩

#print axioms htabSet_call_normal_tables

/-- The deletion bound from the maintained order invariant. -/
theorem runBounded_htabDel_call_tables {F : Type} (state : PanSemStateFiniteExact 64 F) (destination : Option (VarKind × MlS))
    (tableArgument keyArgument : ExpHOL 64)
    (keyLength table keys stride capacity used values order orderPos count key : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits state)
    (tables : OrderInv state capacity count used order orderPos)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [tableArgument,keyArgument] = some [.val (.word table),.val (.word key)])
    (room : count.toNat < capacity.toNat) (small : keyLength.toNat ≤ 33806089496)
    (budget : delBodyCost keyLength capacity + 1 ≤ state.clock) :
    RunBounded state (.call (some (destination,none)) (ofString "htab_del") [tableArgument,keyArgument])
      (delBodyCost keyLength capacity + 1) :=
  runBounded_htabDel_call state destination tableArgument keyArgument keyLength table keys stride capacity used values order
    orderPos count key bits inv args room tables.1 small budget

#print axioms runBounded_htabDel_call_tables
end InitECandidate.Runtime
