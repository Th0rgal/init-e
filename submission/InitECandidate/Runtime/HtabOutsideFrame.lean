import InitECandidate.Runtime.HtabNewFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htabDelMove_normalRel : NormalRel HeapRel htabDelMove := by
  have pre := heapRel_preorder
  rw [htabDelMove_shape]
  exact normalRel_seq pre (normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_memcpy_lookup memcpy_returnedRel)
    (heapRel_leaf (fun _ => rfl))

theorem htabDelBody_normalRel : NormalRel HeapRel htabDelBody := by
  have pre := heapRel_preorder
  rw [htabDelBody_cont_shape]
  apply normalRel_seq pre (heapRel_leaf (fun _ => rfl))
  apply normalRel_seq pre (heapRel_leaf (fun _ => rfl))
  apply normalRel_decCall pre _ _ _ _ _ _ _ originalRuntimeCode_hash_lookup
    (NormalRel.returned (normalRel_readOnly pre htabHash_readOnly))
  unfold htabDelCont
  apply normalRel_dec pre
  apply normalRel_dec pre
  exact normalRel_seq pre (heapRel_leaf (fun _ => rfl)) (normalRel_ite pre _ htabDelMove_normalRel (heapRel_leaf (fun _ => rfl)))

/-- The original deletion keeps every global on continuing outcomes. -/
theorem htabDel_normalRel : NormalRel HeapRel (sourceFunctionBody Guest.guestFn_htab_del) := by
  have pre := heapRel_preorder
  rw [source_htabDel_afterFind]
  have findRel : ReturnedRel HeapRel (sourceFunctionBody Guest.guestFn_htab_find_slot) := by
    apply NormalRel.returned
    apply normalRel_of_frame pre
    intro F state code
    exact (htabFindSlot_memoryFrame state code).2
  apply normalRel_decCall pre _ _ _ _ _ _ _ originalRuntimeCode_hashFind_lookup findRel
  rw [htabDelAfterFind_shape]
  apply normalRel_dec pre
  apply normalRel_seq pre (heapRel_leaf (fun _ => rfl))
  rw [htabDelHeaders_shape]
  repeat apply normalRel_dec pre
  exact normalRel_seq pre (normalRel_while pre _ htabDelBody_normalRel) (heapRel_leaf (fun _ => rfl))

/-- Discarded `htab_del` calls keep every global. -/
theorem htabDel_call_normalRel (arguments : List (ExpHOL 64)) :
    NormalRel HeapRel (.call (some (none,none)) (ofString "htab_del") arguments) :=
  normalRel_discard_call heapRel_preorder _ _ _ _ _ originalRuntimeCode_hashDelete_lookup (NormalRel.returned htabDel_normalRel)

#print axioms htabDel_normalRel
#print axioms htabDel_call_normalRel

/-- The original constructor keeps every non-heap global and moves an aligned
in-arena heap word only upward inside the arena, on continuing outcomes. -/
theorem htabNew_normalRel : NormalRel HeapRel (sourceFunctionBody Guest.guestFn_htab_new) := by
  have pre := heapRel_preorder
  rw [source_htabNew_body]
  repeat (first
    | apply normalRel_decCall pre _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup alloc_returnedRel
    | apply normalRel_dec pre
    | apply normalRel_seq pre (normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_memzero_lookup memzero_returnedRel)
    | apply normalRel_seq pre (heapRel_leaf (fun _ => rfl))
    | exact heapRel_leaf (fun _ => rfl))

#print axioms htabNew_normalRel

/-- Memory outside the table region agrees with a fixed memory. -/
def OutsideSame {F : Type} (s : PanSemStateFiniteExact 64 F) (M : BitVec 64 → HolWordLab 64) (table capacity orderPos : BitVec 64) : Prop :=
  ∀ w : BitVec 64, (w.toNat < table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ w.toNat) → s.memory w = M w

/-- Backward-shift state that also keeps the memory outside the table region. -/
structure DelStateE2 {F : Type} (keyLength table keys stride capacity used values order orderPos count empty : BitVec 64)
    (bits : Nat) (occ : BitVec 64 → Option UInt8) (M : BitVec 64 → HolWordLab 64) (s : PanSemStateFiniteExact 64 F)
    (I J : BitVec 64) : Prop extends
    DelStateE keyLength table keys stride capacity used values order orderPos count empty bits occ s I J where
  out : OutsideSame s M table capacity orderPos

theorem DelStateE2.congr {F : Type} {s r : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count empty : BitVec 64} {bits : Nat} {occ : BitVec 64 → Option UInt8} {M : BitVec 64 → HolWordLab 64} {I J : BitVec 64}
    (d : DelStateE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M s I J)
    (header : ∀ k : Nat, k ≤ 64 → r.memory (table + BitVec.ofNat 64 k) = s.memory (table + BitVec.ofNat 64 k))
    (occupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      r.memory (panByteAlignHOL (used + slot)) = s.memory (panByteAlignHOL (used + slot)))
    (positions : ∀ q : BitVec 64, q.toNat < capacity.toNat → r.memory (orderPos + q * 8) = s.memory (orderPos + q * 8))
    (cells : ∀ k : BitVec 64, k.toNat < count.toNat → r.memory (order + k * 8) = s.memory (order + k * 8))
    (outside : ∀ w : BitVec 64, (w.toNat < table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ w.toNat) → r.memory w = s.memory w)
    (addresses : r.memaddrs = s.memaddrs) (endian : r.be = s.be) (code : r.code = s.code)
    (locals : ∀ k ∈ delLocalNames, r.locals.lookup k = s.locals.lookup k) :
    DelStateE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M r I J :=
  ⟨d.toDelStateE.congr header occupancy positions cells addresses endian code locals,
    fun w h => (outside w h).trans (d.out w h)⟩

theorem DelStateE2.setOther {F : Type} {s : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count empty : BitVec 64} {bits : Nat} {occ : BitVec 64 → Option UInt8} {M : BitVec 64 → HolWordLab 64} {I J : BitVec 64}
    (d : DelStateE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M s I J) (name : MlS) (value : ValueHOL 64) (fresh : name ∉ delLocalNames) :
    DelStateE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M (setVarHOLFinite name value s) I J :=
  ⟨d.toDelStateE.setOther name value fresh,d.out⟩

theorem DelStateE2.setJ {F : Type} {s : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count empty : BitVec 64} {bits : Nat} {occ : BitVec 64 → Option UInt8} {M : BitVec 64 → HolWordLab 64} {I J : BitVec 64}
    (d : DelStateE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M s I J) (J' : BitVec 64) (inside : J'.toNat < capacity.toNat) :
    DelStateE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M (setVarHOLFinite (ofString "j") (.val (.word J')) s) I J' :=
  ⟨d.toDelStateE.setJ J' inside,d.out⟩

theorem DelStateE2.clock {F : Type} {s : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count empty : BitVec 64} {bits : Nat} {occ : BitVec 64 → Option UInt8} {M : BitVec 64 → HolWordLab 64} {I J : BitVec 64}
    (d : DelStateE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M s I J) : DelStateE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M (decClockHOLFinite s) I J :=
  ⟨d.toDelStateE.clock,d.out⟩

theorem DelStateE2.ofDec {F : Type} {inner post : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count empty : BitVec 64} {bits : Nat} {occ : BitVec 64 → Option UInt8} {M : BitVec 64 → HolWordLab 64} {I J : BitVec 64}
    (d : DelStateE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M inner I J) {name : MlS} (fresh : name ∉ delLocalNames)
    (pm : post.memory = inner.memory) (pa : post.memaddrs = inner.memaddrs) (pb : post.be = inner.be)
    (pc : post.code = inner.code) (plocals : ∀ k, k ≠ name → post.locals.lookup k = inner.locals.lookup k) :
    DelStateE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M post I J :=
  ⟨d.toDelStateE.ofDec fresh pm pa pb pc plocals,fun w h => by rw [pm]; exact d.out w h⟩

theorem htabDelMovableE2_normal {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count empty : BitVec 64} {bits : Nat} {occ : BitVec 64 → Option UInt8} {M : BitVec 64 → HolWordLab 64} {I J : BitVec 64}
    (d : DelStateE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M s I J) (run : evaluateHOLFiniteState s htabDelMovable = (none,post)) :
    DelStateE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M post I J := by
  have memory := (memoryFrame_leaf _ htabDelMovable_readOnly s d.d.inv.code).1
  rw [run] at memory
  exact ⟨htabDelMovableE_normal d.toDelStateE run,fun w h => by rw [memory]; exact d.out w h⟩

#print axioms DelStateE2.congr
#print axioms htabDelMovableE2_normal

theorem htabDelMoveE2_normal {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count empty : BitVec 64} {bits : Nat} {occ : BitVec 64 → Option UInt8} {M : BitVec 64 → HolWordLab 64} {I J : BitVec 64}
    (dE : DelStateE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M s I J)
    (occupied : hashOccupancyRead s used J ≠ some 0) (occJ : occ J ≠ some 0)
    (budget : keyLength.toNat / 32 + keyLength.toNat / 8 + 11 ≤ s.clock)
    (run : evaluateHOLFiniteState s htabDelMove = (none,post)) :
    DelStateE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M post J J := by
  have d := dE.d
  have dE1 := dE.toDelStateE
  have inv := d.inv
  have countLe : count.toNat ≤ capacity.toNat := by
    rw [inv.agreement]; unfold hashOccupiedCount; exact (List.countP_le_length).trans (by simp)
  have iN := inv.slot_toNat I d.iInside
  have jN := inv.slot_toNat J d.jInside
  have capPos : 0 < capacity.toNat := by rw [inv.power]; exact Nat.two_pow_pos bits
  have strideLe : stride.toNat ≤ capacity.toNat * stride.toNat := Nat.le_mul_of_pos_left _ capPos
  have kb := inv.keysBefore; have vb := inv.valuesBefore; have ub := inv.usedBefore; have ob := inv.orderBefore
  have eb := inv.endBound; have fits := inv.fits; have hk := inv.headerKeys; have hv := inv.headerValues
  have small : keyLength.toNat ≤ 33806089496 := by omega
  have iIn := d.iInside; have jIn := d.jInside
  rw [htabDelMove_shape] at run
  obtain ⟨c,copyRun,run⟩ := seq_normal_parts run
  -- the key copy
  have copyArgs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "i"),.var .local (ofString "stride")]],
       .op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "j"),.var .local (ofString "stride")]],
       .var .local (ofString "klen")] =
        some [.val (.word (keys + I * stride)),.val (.word (keys + J * stride)),.val (.word keyLength)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,d.keysL,d.iL,d.jL,d.strideL,d.klenL,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]
  have dstAligned : (keys + I * stride).toNat % 8 = 0 := by
    rw [iN.2.2.2.1]; have := delStride_mod (I := I) inv.strideAligned; have := inv.keysAligned; omega
  have copyFrame : ∀ watched : BitVec 64,
      (watched.toNat < (keys + I * stride).toNat ∨ (keys + I * stride).toNat + keyLength.toNat ≤ watched.toNat) →
      c.memory watched = s.memory watched := by
    intro watched outside
    have separated := memcpy_interval_separate (keys + I * stride) keyLength watched dstAligned
      (by rw [iN.2.2.2.1]; have := iN.2.2.2.2; omega) outside
    exact memcpy_call_normal_memory s c _ (keys + I * stride) (keys + J * stride) keyLength watched copyArgs
      inv.code (fun o ho => (separated o ho).1) (fun o ho => (separated o ho).2) small budget copyRun
  have copyMeta := evaluateHOLFiniteState_metadata s (.call (some (none,none)) (ofString "memcpy")
    [.op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "i"),.var .local (ofString "stride")]],
     .op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "j"),.var .local (ofString "stride")]],
     .var .local (ofString "klen")])
  rw [copyRun] at copyMeta
  have copyLocal : ∀ k : MlS, c.locals.lookup k = s.locals.lookup k := by
    intro k
    have kept := evaluate_avoidsLocal_flowing k (.call (some (none,none)) (ofString "memcpy")
      [.op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "i"),.var .local (ofString "stride")]],
       .op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "j"),.var .local (ofString "stride")]],
       .var .local (ofString "klen")]) (by simp [avoidsLocal]) s (by rw [copyRun]; exact Or.inl rfl)
    rw [copyRun] at kept
    exact kept
  have iDst := iN.2.2.2.1; have iEnd := iN.2.2.2.2
  have byteNat : ∀ q : BitVec 64, q.toNat < capacity.toNat → (panByteAlignHOL (used + q)).toNat = (used.toNat + q.toNat) / 8 * 8 := by
    intro q inside
    rw [byteAlign_toNat,BitVec.toNat_add_of_lt (by omega)]
  have dc : DelState keyLength table keys stride capacity used values order orderPos count empty bits occ c I J :=
    d.congr
      (fun k hk' => copyFrame _ (Or.inl (by
        rw [word_add_toNat table k (by have := keys.isLt; omega),iDst]; omega)))
      (fun q inside => copyFrame _ (Or.inr (by
        rw [byteNat q inside,iDst]; have := inv.usedAligned; omega)))
      (fun q inside => copyFrame _ (Or.inr (by
        rw [(inv.slot_toNat q inside).2.2.1,iDst]; omega)))
      copyMeta.2.1 copyMeta.2.2.1 copyMeta.1 (fun k _ => copyLocal k)
  have ec : HashOrderEntriesBound order capacity count c := dE.entries.congr (fun k inside => copyFrame _ (Or.inr (by
    rw [(inv.slot_toNat k (by omega)).2.1,iDst]; omega)))
  have oc : OutsideSame c M table capacity orderPos := fun w h => (copyFrame w (by
    have := inv.headerKeys; rcases h with h | h
    · left; rw [iDst]; omega
    · right; rw [iDst]; omega)).trans (dE.out w h)
  have cOcc : hashOccupancyRead c used J = hashOccupancyRead s used J :=
    occupancyRead_congr_at c s used J (copyFrame _ (Or.inr (by rw [byteNat J d.jInside,iDst]; have := inv.usedAligned; omega)))
      copyMeta.2.1 copyMeta.2.2.1
  -- the value move
  obtain ⟨c2,valRun,run⟩ := seq_normal_parts run
  have cInv := dc.inv
  have domainAt : ∀ base : BitVec 64, ∀ q : BitVec 64, base.toNat % 8 = 0 → table.toNat ≤ base.toNat →
      (base + q * 8).toNat = base.toNat + q.toNat * 8 → base.toNat + q.toNat * 8 < orderPos.toNat + capacity.toNat * 8 →
      c.memaddrs (base + q * 8) := by
    intro base q a1 a2 e a3
    exact cInv.domain _ (by rw [e]; omega) (by rw [e]; omega) (by rw [e]; omega)
  obtain ⟨jv,hjv⟩ : ∃ x : BitVec 64, c.memory (values + J * 8) = .word x := by
    cases h : c.memory (values + J * 8) with
    | word x => exact ⟨x,rfl⟩
  have c2Eq := store_word_normal c c2 _ _ (values + I * 8) jv
    (eval_delScaled8 c _ _ values I dc.valsL dc.iL)
    (eval_delLoad c _ (values + J * 8) jv (eval_delScaled8 c _ _ values J dc.valsL dc.jL)
      (domainAt values J inv.valuesAligned (by omega) jN.1 (by omega)) hjv) valRun
  subst c2Eq
  have dc2 := dc.write_region (values + I * 8) jv
    (fun k hk' => by
      apply word_ne_of_toNat
      rw [iN.1,word_add_toNat table k (by have := values.isLt; omega)]; omega)
    (fun q inside => by
      apply word_ne_of_toNat
      rw [iN.1,byteNat q inside]; have := inv.usedAligned; have := inv.valuesAligned; omega)
    (fun q inside => by
      apply word_ne_of_toNat
      rw [iN.1,(inv.slot_toNat q inside).2.2.1]; omega)
  have c2Occ : hashOccupancyRead (sourceWriteWord c (values + I * 8) jv) used J ≠ some 0 := by
    rw [occupancyRead_congr_at (sourceWriteWord c (values + I * 8) jv) c used J (by
      simp only [sourceWriteWord]
      rw [if_neg]
      intro h
      have := congrArg BitVec.toNat h
      rw [iN.1,byteNat J d.jInside] at this
      have := inv.usedAligned; have := inv.valuesAligned; omega) rfl rfl,cOcc]
    exact occupied
  have ec2 : HashOrderEntriesBound order capacity count (sourceWriteWord c (values + I * 8) jv) :=
    ec.congr (fun k inside => by
      simp only [sourceWriteWord]
      rw [if_neg (word_ne_of_toNat (by rw [(inv.slot_toNat k (by omega)).2.1,iN.1]; omega))])
  have oc2 : OutsideSame (sourceWriteWord c (values + I * 8) jv) M table capacity orderPos := fun w h => by
    simp only [sourceWriteWord]
    rw [if_neg (word_ne_of_toNat (by rw [iN.1]; have := inv.headerValues; omega))]
    exact oc w h
  generalize sourceWriteWord c (values + I * 8) jv = c2 at dc2 c2Occ run ec2 oc2
  -- the moved order position
  obtain ⟨value,inner,hval,innerRun,pm,pa,pb,pc,_,plocals,_⟩ := dec_normal_state run
  obtain ⟨x,hx,xlt⟩ := dc2.orderPosOK J jIn c2Occ
  have inv2 := dc2.inv
  rw [eval_delLoad c2 _ (orderPos + J * 8) x (eval_delScaled8 c2 _ _ orderPos J dc2.orderPosL dc2.jL)
    (inv2.domain _ (by rw [jN.2.2.1]; have := inv.orderPosAligned; omega) (by rw [jN.2.2.1]; omega)
      (by rw [jN.2.2.1]; omega)) hx] at hval
  cases hval
  have dc3 := dc2.setOther (ofString "moved_pos") (.val (.word x)) (by decide)
  have movedL : (setVarHOLFinite (ofString "moved_pos") (.val (.word x)) c2).locals.lookup (ofString "moved_pos") =
      some (.val (.word x)) := by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have ec3 : HashOrderEntriesBound order capacity count (setVarHOLFinite (ofString "moved_pos") (.val (.word x)) c2) :=
    ec2.congr (fun _ _ => rfl)
  have oc3 : OutsideSame (setVarHOLFinite (ofString "moved_pos") (.val (.word x)) c2) M table capacity orderPos := oc2
  generalize setVarHOLFinite (ofString "moved_pos") (.val (.word x)) c2 = c3 at dc3 movedL innerRun ec3 oc3
  rw [htabDelMoveRest_shape] at innerRun
  obtain ⟨c4,orderRun,innerRun⟩ := seq_normal_parts innerRun
  have c4Eq := store_word_normal c3 c4 _ _ (order + x * 8) I
    (eval_delScaled8 c3 _ _ order x dc3.orderL movedL) (eval_delVar c3 _ I dc3.iL) orderRun
  subst c4Eq
  have xN := inv.slot_toNat x xlt
  have dc4 := dc3.write_region (order + x * 8) I
    (fun k hk' => by
      apply word_ne_of_toNat
      rw [xN.2.1,word_add_toNat table k (by have := values.isLt; omega)]; omega)
    (fun q inside => by
      apply word_ne_of_toNat
      rw [xN.2.1,byteNat q inside]; have := inv.usedAligned; have := inv.orderAligned; omega)
    (fun q inside => by
      apply word_ne_of_toNat
      rw [xN.2.1,(inv.slot_toNat q inside).2.2.1]; omega)
  have movedL4 : (sourceWriteWord c3 (order + x * 8) I).locals.lookup (ofString "moved_pos") = some (.val (.word x)) := movedL
  have ec4 := ec3.write_slot x I iIn (fun k inside same => by
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat same
    rw [(inv.slot_toNat k (by omega)).2.1,xN.2.1] at this
    omega)
  have oc4 : OutsideSame (sourceWriteWord c3 (order + x * 8) I) M table capacity orderPos := fun w h => by
    simp only [sourceWriteWord]
    rw [if_neg (word_ne_of_toNat (by rw [xN.2.1]; have := inv.headerKeys; omega))]
    exact oc3 w h
  generalize sourceWriteWord c3 (order + x * 8) I = c4 at dc4 movedL4 innerRun ec4 oc4
  obtain ⟨c5,posRun,assignRun⟩ := seq_normal_parts innerRun
  have c5Eq := store_word_normal c4 c5 _ _ (orderPos + I * 8) x
    (eval_delScaled8 c4 _ _ orderPos I dc4.orderPosL dc4.iL) (eval_delVar c4 _ x movedL4) posRun
  subst c5Eq
  have dc5 := dc4.write_position I x iIn xlt
  have ec5 : HashOrderEntriesBound order capacity count (sourceWriteWord c4 (orderPos + I * 8) x) :=
    ec4.congr (fun k inside => by
      simp only [sourceWriteWord]
      rw [if_neg (word_ne_of_toNat (by rw [(inv.slot_toNat k (by omega)).2.1,iN.2.2.1]; omega))])
  have oc5 : OutsideSame (sourceWriteWord c4 (orderPos + I * 8) x) M table capacity orderPos := fun w h => by
    simp only [sourceWriteWord]
    rw [if_neg (word_ne_of_toNat (by rw [iN.2.2.1]; have := inv.headerKeys; omega))]
    exact oc4 w h
  generalize sourceWriteWord c4 (orderPos + I * 8) x = c5 at dc5 assignRun ec5 oc5
  rw [evaluate_delAssign c5 (ofString "i") (ofString "j") J I dc5.jL dc5.iL] at assignRun
  cases assignRun
  have dc6 := dc5.setI J jIn
  exact ⟨⟨dc6.congr (fun _ _ => by rw [pm]) (fun _ _ => by rw [pm]) (fun _ _ => by rw [pm]) pa pb pc
    (fun k member => plocals k (by intro h; subst h; revert member; decide)),occJ,
    ec5.congr (fun _ _ => by rw [pm]; rfl)⟩,fun w h => by rw [pm]; exact oc5 w h⟩

#print axioms htabDelMoveE2_normal

theorem htabDelContE2_run {F : Type} {r : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count empty : BitVec 64} {bits : Nat} {occ : BitVec 64 → Option UInt8} {M : BitVec 64 → HolWordLab 64} {I J : BitVec 64}
    (d : DelStateE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M r I J)
    (occupied : occ J ≠ some 0) (budget : delMoveCost keyLength ≤ r.clock) :
    RunBounded r htabDelCont (delMoveCost keyLength) ∧
      ∀ post, evaluateHOLFiniteState r htabDelCont = (none,post) →
        ∃ I', DelStateE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M post I' J := by
  have code := d.d.inv.code
  constructor
  · apply RunBounded.dec
    intro v _
    apply RunBounded.dec
    intro v2 _
    have d2 := (d.setOther (ofString "home") v (by decide)).setOther (ofString "movable") v2 (by decide)
    refine (RunBounded.seq (a := 0) (RunBounded.ofProg (ProgBounded.straight _ htabDelMovable_straight) d2.d.inv.code
      (Nat.zero_le _)) (by simp [setVarHOLFinite]; omega) ?_).weaken (by omega)
    intro next run _ nb
    have dn := htabDelMovableE2_normal d2 run
    apply RunBounded.ite_cases
    · exact runBounded_htabDelMove dn.d nb
    · exact (RunBounded.ofProg (ProgBounded.straight _ (by decide)) dn.d.inv.code (Nat.zero_le _)).weaken (by omega)
  · intro post run
    obtain ⟨v,inner,_,innerRun,pm,pa,pb,pc,_,plocals,_⟩ := dec_normal_state run
    obtain ⟨v2,inner2,_,innerRun2,pm2,pa2,pb2,pc2,_,plocals2,_⟩ := dec_normal_state innerRun
    obtain ⟨mid,movRun,iteRun⟩ := seq_normal_parts innerRun2
    have d2 := (d.setOther (ofString "home") v (by decide)).setOther (ofString "movable") v2 (by decide)
    have dm := htabDelMovableE2_normal d2 movRun
    have clockKept := (RunBounded.ofProg (state := setVarHOLFinite (ofString "movable") v2 (setVarHOLFinite (ofString "home") v r))
      (ProgBounded.straight _ htabDelMovable_straight) d2.d.inv.code (Nat.zero_le _)).1
    rw [movRun] at clockKept
    simp only [setVarHOLFinite] at clockKept
    have finish : ∀ I', DelStateE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M inner2 I' J →
        ∃ I', DelStateE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M post I' J :=
      fun I' di => ⟨I',(di.ofDec (by decide) pm2 pa2 pb2 pc2 plocals2).ofDec (by decide) pm pa pb pc plocals⟩
    rcases ite_normal_cases mid inner2 _ _ _ iteRun with moved | skipped
    · exact finish J (htabDelMoveE2_normal dm (by rw [dm.d.bytes J dm.d.jInside]; exact occupied) occupied (by unfold delMoveCost at budget; omega) moved)
    · rw [evaluateHOLFiniteState_skip] at skipped
      cases skipped
      exact finish I dm

#print axioms htabDelContE2_run

theorem htabDelHashE2_run {F : Type} {r : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count empty : BitVec 64} {bits : Nat} {occ : BitVec 64 → Option UInt8} {M : BitVec 64 → HolWordLab 64} {I J : BitVec 64}
    (d : DelStateE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M r I J)
    (occupied : occ J ≠ some 0) (budget : delIterCost keyLength ≤ r.clock) :
    let call : ProgHOL 64 := .decCall (ofString "h") .one (ofString "htab_hash")
      [.op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "j"),.var .local (ofString "stride")]],
       .var .local (ofString "klen")] htabDelCont
    RunBounded r call (delIterCost keyLength) ∧
      ∀ post, evaluateHOLFiniteState r call = (none,post) →
        ∃ I', DelStateE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M post I' J := by
  intro call
  have inv := d.d.inv
  have capPos : 0 < capacity.toNat := by rw [inv.power]; exact Nat.two_pow_pos bits
  have strideLe : stride.toNat ≤ capacity.toNat * stride.toNat := Nat.le_mul_of_pos_left _ capPos
  have kb := inv.keysBefore; have ub := inv.usedBefore; have ob := inv.orderBefore
  have eb := inv.endBound; have fits := inv.fits
  have small : keyLength.toNat < 2 ^ 62 := by omega
  have args : evalListHOLFinite r (h := fun a => Classical.propDecidable (r.memaddrs a))
      [.op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "j"),.var .local (ofString "stride")]],
       .var .local (ofString "klen")] = some [.val (.word (keys + J * stride)),.val (.word keyLength)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,d.d.keysL,d.d.jL,d.d.strideL,d.d.klenL,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]
  -- the resumed state after any returned hash run
  have resume : ∀ (value : ValueHOL 64) (post : PanSemStateFiniteExact 64 F), post.code = r.code → post.memory = r.memory →
      post.memaddrs = r.memaddrs → post.be = r.be →
      DelStateE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M
        (setVarHOLFinite (ofString "h") value {post with locals := r.locals}) I J := by
    intro value post c m a b
    have d' : DelStateE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M
        {post with locals := r.locals} I J :=
      d.congr (fun _ _ => by simp only [m]) (fun _ _ => by simp only [m]) (fun _ _ => by simp only [m]) (fun _ _ => by simp only [m]) (fun _ _ => by simp only [m]) a b c (fun _ _ => rfl)
    exact d'.setOther _ _ (by decide)
  constructor
  · unfold delIterCost at budget ⊢
    refine runBounded_htabHash_decCall r (ofString "h") _ _ htabDelCont (keys + J * stride) keyLength inv.code args small
      budget ?_
    intro value post c m a b _ tc
    exact (htabDelContE2_run (resume value post c m a b) occupied tc).1
  · intro post run
    obtain ⟨values,body,callee,returnShape,w,bodyPost,resumed,inner,args',lookup,bodyRun,rm,ra,rb,rc,rclk,_,rlocals,
      contRun,pm,pa,pb,pc,pl⟩ := decCall_normal_body run
    rw [args] at args'
    cases args'
    have installed : r.code.lookup (ofString "htab_hash") =
        some ([(ofString "p",.one),(ofString "key_len",.one)],sourceFunctionBody Guest.guestFn_htab_hash,.one) := by
      rw [inv.code]; exact originalRuntimeCode_hash_lookup
    rw [pan_two_word_lookup r.code.lookup (ofString "htab_hash") (ofString "p") (ofString "key_len")
      (sourceFunctionBody Guest.guestFn_htab_hash) (keys + J * stride) keyLength (by decide) installed] at lookup
    cases lookup
    have entryBound := evaluate_htabHash_body_bounded (callEntryStateHOLFinite r ((HolFiniteMapExact.empty.update
        (ofString "p",.val (.word (keys + J * stride)))).update (ofString "key_len",.val (.word keyLength))))
      (by exact inv.code) keyLength (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) small
      (by change _ ≤ r.clock - 1; unfold delIterCost at budget; omega)
    have memory := evaluate_readOnly_memory _ htabHash_readOnly (callEntryStateHOLFinite r ((HolFiniteMapExact.empty.update
        (ofString "p",.val (.word (keys + J * stride)))).update (ofString "key_len",.val (.word keyLength))))
    have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite r ((HolFiniteMapExact.empty.update
        (ofString "p",.val (.word (keys + J * stride)))).update (ofString "key_len",.val (.word keyLength))))
      (sourceFunctionBody Guest.guestFn_htab_hash)
    unfold RunBounded at entryBound
    rw [bodyRun] at memory meta' entryBound
    obtain ⟨spent,kept,_⟩ := entryBound
    have resumedClock := rclk kept
    have dr : DelStateE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M resumed I J :=
      d.congr (fun _ _ => by rw [rm,memory]; rfl) (fun _ _ => by rw [rm,memory]; rfl) (fun _ _ => by rw [rm,memory]; rfl) (fun _ _ => by rw [rm,memory]; rfl) (fun _ _ => by rw [rm,memory]; rfl)
        (ra.trans meta'.2.1) (rb.trans meta'.2.2.1) (rc.trans meta'.1)
        (fun k member => rlocals k (fun h => by subst h; revert member; decide))
    obtain ⟨I',di⟩ := (htabDelContE2_run dr occupied (by
      change r.clock - 1 ≤ bodyPost.clock + _ at spent
      unfold delIterCost at budget; omega)).2 inner contRun
    exact ⟨I',di.congr (fun _ _ => by rw [pm]) (fun _ _ => by rw [pm]) (fun _ _ => by rw [pm]) (fun _ _ => by rw [pm]) (fun _ _ => by rw [pm]) pa pb pc
      (fun k member => pl k (fun h => by subst h; revert member; decide))⟩

#print axioms htabDelHashE2_run

theorem htabDelBodyE2_run {F : Type} {t : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count empty : BitVec 64} {bits : Nat} {occ : BitVec 64 → Option UInt8} {M : BitVec 64 → HolWordLab 64} {I J : BitVec 64}
    (d : DelStateE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M t I J)
    (budget : delIterCost keyLength ≤ t.clock) :
    RunBounded t htabDelBody (delIterCost keyLength) ∧
      (∀ post, evaluateHOLFiniteState t htabDelBody = (none,post) → occ (hashProbeNext J capacity) ≠ some 0 ∧
        ∃ I', DelStateE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M post I'
          (hashProbeNext J capacity)) ∧
      (∀ post, evaluateHOLFiniteState t htabDelBody = (some .break,post) → occ (hashProbeNext J capacity) = some 0 ∧
        ∃ I', DelStateE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M post I'
          (hashProbeNext J capacity)) := by
  have inv := d.d.inv
  have nextInside : (hashProbeNext J capacity).toNat < capacity.toNat := by
    rw [hashProbeNext_toNat J capacity bits inv.power d.d.jInside]
    exact Nat.mod_lt _ (by rw [inv.power]; exact Nat.two_pow_pos bits)
  have d1 := d.setJ _ nextInside
  rw [htabDelBody_cont_shape]
  have whole := evaluateHOLFiniteState_seq_line780 t (hashProbeStep (ofString "j"))
    (.seq (.ite (.cmp .equal (.loadByte (.op .add [.var .local (ofString "used"),.var .local (ofString "j")])) (.const 0))
          .break .skip)
        (.decCall (ofString "h") .one (ofString "htab_hash")
            [.op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "j"),.var .local (ofString "stride")]],
             .var .local (ofString "klen")] htabDelCont))
  rw [evaluate_hashProbeStep t (ofString "j") J capacity d.d.jL d.d.capL] at whole
  dsimp only at whole
  have clk : (setVarHOLFinite (ofString "j") (.val (.word (hashProbeNext J capacity))) t).clock = t.clock := rfl
  generalize setVarHOLFinite (ofString "j") (.val (.word (hashProbeNext J capacity))) t = t1 at d1 whole clk
  unfold RunBounded
  rw [whole]
  have restSeq := fun (x : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F) (h : evaluateHOLFiniteState t1
      (.ite (.cmp .equal (.loadByte (.op .add [.var .local (ofString "used"),.var .local (ofString "j")])) (.const 0))
          .break .skip) = x) => (evaluateHOLFiniteState_seq_line780 t1 _ (.decCall (ofString "h") .one (ofString "htab_hash")
            [.op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "j"),.var .local (ofString "stride")]],
             .var .local (ofString "klen")] htabDelCont)).trans (by rw [h])
  have read := d1.d.bytes _ nextInside
  cases hb : occ (hashProbeNext J capacity) with
  | none =>
    rw [hb] at read
    have rest := restSeq _ (evaluate_delBreakCheck_none t1 used _ .break .skip d1.d.usedL d1.d.jL read)
    dsimp only at rest
    rw [rest]
    dsimp only
    refine ⟨⟨by omega,by omega,by simp⟩,fun post h => by simp at h,fun post h => by simp at h⟩
  | some b =>
    rw [hb] at read
    have ite := evaluate_loaded_word_ite t1 _ (BitVec.ofNat 64 b.toNat) 0 .equal
      (eval_delLoadByte t1 used _ b d1.d.usedL d1.d.jL read) .break .skip
    by_cases zero : b = 0
    · subst zero
      have iteB : evaluateHOLFiniteState t1
          (.ite (.cmp .equal (.loadByte (.op .add [.var .local (ofString "used"),.var .local (ofString "j")])) (.const 0))
            .break .skip) = (some .break,t1) := by
        rw [ite]; simp [Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_break]
      have rest := restSeq _ iteB
      dsimp only at rest
      rw [rest]
      dsimp only
      refine ⟨⟨by omega,by omega,by simp⟩,fun post h => by simp at h,fun post h => ?_⟩
      simp only [Prod.mk.injEq,true_and] at h
      subst h
      exact ⟨rfl,I,d1⟩
    · have iteS : evaluateHOLFiniteState t1
          (.ite (.cmp .equal (.loadByte (.op .add [.var .local (ofString "used"),.var .local (ofString "j")])) (.const 0))
            .break .skip) = (none,t1) := by
        rw [ite]; simp [Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]; exact byte_word_ne_zero b zero
      have rest := restSeq _ iteS
      dsimp only at rest
      rw [rest]
      have occupied : occ (hashProbeNext J capacity) ≠ some 0 := by
        rw [hb]; intro h; exact zero (Option.some.inj h)
      obtain ⟨bounded,normal⟩ := htabDelHashE2_run d1 occupied (by omega)
      unfold RunBounded at bounded
      refine ⟨⟨by omega,by omega,bounded.2.2⟩,fun post h => ⟨fun e => zero (Option.some.inj e),normal post h⟩,fun post h => ?_⟩
      exact absurd (congrArg Prod.fst h) (evaluate_noTopBreak _ (by decide) t1)

#print axioms htabDelBodyE2_run

def DelRankE2 (keyLength table keys stride capacity used values order orderPos count empty : BitVec 64) (bits : Nat)
    (occ : BitVec 64 → Option UInt8) (M : BitVec 64 → HolWordLab 64) {F : Type} (s : PanSemStateFiniteExact 64 F) (n : Nat) : Prop :=
  ∃ I J, DelStateE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M s I J ∧
    (occ J ≠ some 0 → hashProbeDistance capacity.toNat J.toNat empty.toNat < n) ∧
    (occ J = some 0 → capacity.toNat < n)

/-- The backward-shift loop from rank n runs within n * (iteration + 1) ticks in every outcome. -/
theorem htabDelLoopE2_run (keyLength table keys stride capacity used values order orderPos count empty : BitVec 64) (bits : Nat)
    (occ : BitVec 64 → Option UInt8) (M : BitVec 64 → HolWordLab 64) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
      DelRankE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M state n →
      n * (delIterCost keyLength + 1) ≤ state.clock →
      RankedOutcome state (.const 1) (n * (delIterCost keyLength + 1))
        (DelRankE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M) True
        (evaluateHOLFiniteState state (.while (.const 1) htabDelBody)) := by
  refine rankedWhile_run (.const 1) htabDelBody (delIterCost keyLength)
    (DelRankE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M) True ?_ ?_
  · intro F s ranked w _
    obtain ⟨I,J,_,a,b⟩ := ranked
    by_cases h : occ J = some 0
    · exact absurd (b h) (by omega)
    · exact absurd (a h) (by omega)
  · intro F s n w code ranked _ _ budget
    obtain ⟨I,J,d,a,b⟩ := ranked
    have inv := d.d.inv
    obtain ⟨bounded,normal,broken⟩ := htabDelBodyE2_run d.clock (by change _ ≤ s.clock - 1; omega)
    unfold RunBounded at bounded
    obtain ⟨spent,kept,safe⟩ := bounded
    have nextInside : (hashProbeNext J capacity).toNat < capacity.toNat := by
      rw [hashProbeNext_toNat J capacity bits inv.power d.d.jInside]
      exact Nat.mod_lt _ (by rw [inv.power]; exact Nat.two_pow_pos bits)
    have farNext := hashProbeDistance_lt_capacity capacity.toNat (hashProbeNext J capacity).toNat empty.toNat nextInside
      d.d.emptyInside
    refine ⟨spent,kept,safe,?_,?_⟩
    · intro flow
      rcases flow with flow | flow
      · obtain ⟨occupied,I',d'⟩ := normal _ (Prod.ext flow rfl)
        refine ⟨n,le_refl _,⟨I',hashProbeNext J capacity,d',fun _ => ?_,fun h => absurd h occupied⟩,d'.d.inv.code.trans code.symm⟩
        by_cases here : occ J = some 0
        · have := b here; omega
        · have far := a here
          have differs : J.toNat ≠ empty.toNat := by
            intro same
            have equal : J = empty := BitVec.eq_of_toNat_eq same
            exact here (equal ▸ d.d.emptyByte)
          have decreased := hashProbeDistance_decreases capacity.toNat J.toNat empty.toNat d.d.jInside d.d.emptyInside differs
          rw [← hashProbeNext_wrap J capacity bits inv.power d.d.jInside] at decreased
          omega
      · exact absurd flow (evaluate_noTopContinue _ (by decide) _)
    · intro flow
      obtain ⟨_,I',d'⟩ := broken _ (Prod.ext flow rfl)
      exact ⟨trivial,capacity.toNat + 1,⟨I',hashProbeNext J capacity,d',fun _ => by omega,fun _ => by omega⟩,
        d'.d.inv.code.trans code.symm⟩

#print axioms htabDelLoopE2_run

theorem htabDelTail_returnedE2 {F : Type} {X post : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count empty : BitVec 64} {bits : Nat} {occ : BitVec 64 → Option UInt8} {M : BitVec 64 → HolWordLab 64} {I J : BitVec 64}
    (d : DelStateE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M X I J)
    (tL : X.locals.lookup (ofString "t") = some (.val (.word table)))
    (dp : BitVec 64) (dpL : X.locals.lookup (ofString "deleted_pos") = some (.val (.word dp)))
    (dpLt : dp.toNat < capacity.toNat) (v : ValueHOL 64)
    (run : evaluateHOLFiniteState X htabDelTail = (some (.returned v),post)) :
    ∃ count' : BitVec 64, count'.toNat + 1 = count.toNat ∧
      HtabAligned keyLength table keys stride capacity used values order orderPos count' bits post ∧
      OrderInv post capacity count' used order orderPos ∧ post.memaddrs = X.memaddrs ∧ post.be = X.be ∧
      OutsideSame post M table capacity orderPos := by
  have dd := d.d
  have inv := dd.inv
  have iIn := dd.iInside
  have holeRead : hashOccupancyRead X used I ≠ some 0 := by rw [dd.bytes I iIn]; exact d.holeOcc
  have countLe : count.toNat ≤ capacity.toNat := by
    rw [inv.agreement]; unfold hashOccupiedCount; exact (List.countP_le_length).trans (by simp)
  have countPos : 1 ≤ count.toNat := by
    by_cases z : count.toNat = 0
    · exact absurd (hashOccupiedCount_zero_reads capacity (hashOccupancyRead X used) (by rw [← inv.agreement]; exact z) I iIn)
        holeRead
    · omega
  have kb := inv.keysBefore; have vb := inv.valuesBefore; have ub := inv.usedBefore; have ob := inv.orderBefore
  have eb := inv.endBound; have hk := inv.headerKeys; have hv := inv.headerValues
  have tFits : table.toNat + 72 < 2 ^ 64 := by have := keys.isLt; omega
  have hdr : ∀ k : Nat, k ≤ 64 → (table + BitVec.ofNat 64 k).toNat = table.toNat + k :=
    fun k hk' => word_add_toNat table k (by omega)
  have byteNat : ∀ q : BitVec 64, q.toNat < capacity.toNat → (panByteAlignHOL (used + q)).toNat = (used.toNat + q.toNat) / 8 * 8 := by
    intro q inside
    rw [byteAlign_toNat,BitVec.toNat_add_of_lt (by omega)]
  have h24 : (table + 24 : BitVec 64).toNat = table.toNat + 24 := hdr 24 (by omega)
  rw [htabDelTail_shape] at run
  -- clear the hole's occupancy byte
  obtain ⟨Y,byteRun,run⟩ := seq_returned_of_nonreturning_first (fun v => evaluate_noTopReturn _ rfl X v) run
  obtain ⟨cell,hcell⟩ : ∃ cell : BitVec 64, X.memory (panByteAlignHOL (used + I)) = .word cell := by
    cases h : X.memory (panByteAlignHOL (used + I)) with
    | word x => exact ⟨x,rfl⟩
  have byteDomain : X.memaddrs (panByteAlignHOL (used + I)) :=
    inv.domain _ (by rw [byteNat I iIn]; omega) (by rw [byteNat I iIn]; have := inv.usedAligned; omega)
      (by rw [byteNat I iIn]; omega)
  rw [evaluate_source_storeByte X _ _ (used + I) 0 cell
    (by simp [evalHOLExact,evalListHOLExact,dd.usedL,dd.iL,wordOpHOL,wordOp,valueIsWord,valueWord])
    (eval_const_word X 0) byteDomain hcell] at byteRun
  cases byteRun
  have cleared := sourceWriteByte_occupancy_clear X capacity used I cell iIn byteDomain hcell holeRead
  have yMem : ∀ a : BitVec 64, a ≠ panByteAlignHOL (used + I) → (sourceWriteByte X (used + I) 0 cell).memory a = X.memory a :=
    fun a ne => sourceWriteByte_memory_other X (used + I) 0 cell a ne
  have yReads : ∀ q : BitVec 64, q ≠ I → hashOccupancyRead (sourceWriteByte X (used + I) 0 cell) used q = hashOccupancyRead X used q := by
    intro q ne
    have addresses : used + q ≠ used + I := by simpa using ne
    exact sourceWriteByte_load_other X (used + I) 0 cell (used + q) addresses hcell
  have yClear : hashOccupancyRead (sourceWriteByte X (used + I) 0 cell) used I = some 0 := by
    have := sourceWriteByte_load_self X (used + I) 0 cell byteDomain
    unfold hashOccupancyRead; rw [show (sourceWriteByte X (used + I) 0 cell).memaddrs = X.memaddrs from rfl,
      show (sourceWriteByte X (used + I) 0 cell).be = X.be from rfl,this]; rfl
  generalize hY : sourceWriteByte X (used + I) 0 cell = Y at run cleared yMem yReads yClear
  have yFacts : Y.memaddrs = X.memaddrs ∧ Y.be = X.be ∧ Y.code = X.code ∧ Y.locals = X.locals := by
    rw [← hY]; exact ⟨rfl,rfl,rfl,rfl⟩
  have farByte : ∀ a : BitVec 64, (a.toNat < used.toNat ∨ used.toNat + capacity.toNat ≤ a.toNat) → a ≠ panByteAlignHOL (used + I) := by
    intro a h e
    have := congrArg BitVec.toNat e
    rw [byteNat I iIn] at this
    have := inv.usedAligned
    omega
  -- n and last_pos
  obtain ⟨vn,in1,en,run1,m1,a1,b1,c1⟩ := dec_returned_state run
  rw [eval_header_load Y _ table 24 count (by rw [yFacts.2.2.2]; exact tL)
    (by rw [yFacts.1]; exact inv.header_domain 24 (by omega) (by omega))
    (by rw [yMem _ (farByte _ (Or.inl (by rw [h24]; omega)))]; exact inv.cell24)] at en
  cases en
  obtain ⟨vl,in2,el,run2,m2,a2,b2,c2⟩ := dec_returned_state run1
  rw [show @evalHOLExact 64 F _ (setVarHOLFinite (ofString "n") (.val (.word count)) Y).toExact
      (fun a => Classical.propDecidable ((setVarHOLFinite (ofString "n") (.val (.word count)) Y).memaddrs a))
      (.op .sub [.var .local (ofString "n"),.const 1]) = some (.val (.word (count - 1))) by
    simp [evalHOLExact,evalListHOLExact,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,wordOpHOL,wordOp,
      valueIsWord,valueWord]] at el
  cases el
  generalize hZ0 : setVarHOLFinite (ofString "last_pos") (.val (.word (count - 1)))
    (setVarHOLFinite (ofString "n") (.val (.word count)) Y) = Z0 at run2
  have z0Facts : Z0.memory = Y.memory ∧ Z0.memaddrs = X.memaddrs ∧ Z0.be = X.be ∧ Z0.code = X.code := by
    rw [← hZ0]; exact ⟨rfl,yFacts.1,yFacts.2.1,yFacts.2.2.1⟩
  have z0L : ∀ k, k ≠ ofString "last_pos" → k ≠ ofString "n" → Z0.locals.lookup k = X.locals.lookup k := by
    intro k n1 n2; rw [← hZ0]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm n1,Ne.symm n2]
    rw [yFacts.2.2.2]
  have z0Last : Z0.locals.lookup (ofString "last_pos") = some (.val (.word (count - 1))) := by
    rw [← hZ0]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have z0T := (z0L _ (by decide) (by decide)).trans tL
  have z0Order := (z0L _ (by decide) (by decide)).trans dd.orderL
  have z0Pos := (z0L _ (by decide) (by decide)).trans dd.orderPosL
  have z0Dp := (z0L _ (by decide) (by decide)).trans dpL
  have cm1 : (count - 1).toNat = count.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 1 ≤ count.toNat; omega))]; rfl
  -- the order swap
  obtain ⟨Z,iteRun,run3⟩ := seq_returned_of_nonreturning_first (fun v => evaluate_noTopReturn _ (by decide) Z0 v) run2
  have zCases : Z.memaddrs = X.memaddrs ∧ Z.be = X.be ∧ Z.code = X.code ∧
      (∀ k, k ≠ ofString "last_slot" → Z.locals.lookup k = Z0.locals.lookup k) ∧
      ((∀ a, Z.memory a = Y.memory a) ∨
        ∃ ls : BitVec 64, ls.toNat < capacity.toNat ∧ ∀ a, Z.memory a =
          if a = orderPos + ls * 8 then .word dp else if a = order + dp * 8 then .word ls else Y.memory a) := by
    rcases ite_normal_cases_cond Z0 Z _ _ _ iteRun with ⟨_,_,_,yes⟩ | ⟨_,no⟩
    · obtain ⟨lv,inner,le,innerRun,pm,pa,pb,pc,_,plocals,_⟩ := dec_normal_state yes
      obtain ⟨ls,hls,lslt⟩ := d.entries (count - 1) (by omega)
      have lastN := inv.slot_toNat (count - 1) (by omega)
      have lastDomain : X.memaddrs (order + (count - 1) * 8) :=
        inv.domain _ (by rw [lastN.2.1]; have := inv.orderAligned; omega) (by rw [lastN.2.1]; omega)
          (by rw [lastN.2.1]; omega)
      have lastCell : Z0.memory (order + (count - 1) * 8) = .word ls := by
        rw [z0Facts.1,yMem _ (farByte _ (Or.inr (by rw [lastN.2.1]; omega)))]; exact hls
      rw [eval_delLoad Z0 _ (order + (count - 1) * 8) ls (eval_delScaled8 Z0 _ _ order (count - 1) z0Order z0Last)
        (by rw [z0Facts.2.1]; exact lastDomain) lastCell] at le
      cases le
      have sL : ∀ k, k ≠ ofString "last_slot" →
          (setVarHOLFinite (ofString "last_slot") (.val (.word ls)) Z0).locals.lookup k = Z0.locals.lookup k := by
        intro k ne; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne]
      have sLs : (setVarHOLFinite (ofString "last_slot") (.val (.word ls)) Z0).locals.lookup (ofString "last_slot") =
          some (.val (.word ls)) := by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      obtain ⟨W1,s1,s2⟩ := seq_normal_parts innerRun
      have w1Eq := store_word_normal _ W1 _ _ (order + dp * 8) ls
        (eval_delScaled8 _ _ _ order dp ((sL _ (by decide)).trans z0Order) ((sL _ (by decide)).trans z0Dp))
        (eval_delVar _ _ ls sLs) s1
      subst w1Eq
      have innerEq := store_word_normal
        (sourceWriteWord (setVarHOLFinite (ofString "last_slot") (.val (.word ls)) Z0) (order + dp * 8) ls) inner _ _
        (orderPos + ls * 8) dp
        (eval_delScaled8 _ _ _ orderPos ls (by exact (sL _ (by decide)).trans z0Pos) (by exact sLs))
        (eval_delVar _ _ dp (by exact (sL _ (by decide)).trans z0Dp)) s2
      subst innerEq
      refine ⟨pa.trans z0Facts.2.1,pb.trans z0Facts.2.2.1,pc.trans z0Facts.2.2.2,fun k ne => (plocals k ne).trans (sL k ne),
        Or.inr ⟨ls,lslt,fun a => by rw [pm,← z0Facts.1]; rfl⟩⟩
    · rw [evaluateHOLFiniteState_skip] at no
      cases no
      exact ⟨z0Facts.2.1,z0Facts.2.2.1,z0Facts.2.2.2,fun _ _ => rfl,Or.inl (fun a => by rw [z0Facts.1])⟩
  obtain ⟨za,zb,zc,zl,zm⟩ := zCases
  have zT : Z.locals.lookup (ofString "t") = some (.val (.word table)) := (zl _ (by decide)).trans z0T
  have zLast : Z.locals.lookup (ofString "last_pos") = some (.val (.word (count - 1))) := (zl _ (by decide)).trans z0Last
  have final := store_seq_returned Z in2 _ _ (table + 24) (count - 1) (eval_hashLocalAddress Z _ table 24 zT)
    (eval_delVar Z _ _ zLast) run3
  obtain ⟨fm,fa,fb,fc⟩ := return_const_state _ in2 1 v final
  have postMem : ∀ a, post.memory a = if a = table + 24 then .word (count - 1) else Z.memory a := by
    intro a; rw [m1,m2,fm]; rfl
  have postAddr : post.memaddrs = X.memaddrs := a1.trans (a2.trans (fa.trans za))
  have postBe : post.be = X.be := b1.trans (b2.trans (fb.trans zb))
  have postCode : post.code = X.code := c1.trans (c2.trans (fc.trans zc))
  have byteSame : ∀ q : BitVec 64, q.toNat < capacity.toNat →
      post.memory (panByteAlignHOL (used + q)) = Y.memory (panByteAlignHOL (used + q)) := by
    intro q inside
    have qb := byteNat q inside
    have ua := inv.usedAligned
    rw [postMem,if_neg (word_ne_of_toNat (by rw [qb,h24]; omega))]
    rcases zm with same | ⟨ls,lslt,hz⟩
    · exact same _
    · rw [hz,if_neg (word_ne_of_toNat (by rw [qb,(inv.slot_toNat ls lslt).2.2.1]; omega)),
        if_neg (word_ne_of_toNat (by rw [qb,(inv.slot_toNat dp dpLt).2.1]; omega))]
  have postReads : ∀ q : BitVec 64, q.toNat < capacity.toNat → hashOccupancyRead post used q = hashOccupancyRead Y used q :=
    fun q inside => occupancyRead_congr_at post Y used q (byteSame q inside) (postAddr.trans yFacts.1.symm)
      (postBe.trans yFacts.2.1.symm)
  have bounded : ∀ a : BitVec 64, a ≠ table + 24 → a ≠ panByteAlignHOL (used + I) →
      (∃ x : BitVec 64, X.memory a = .word x ∧ x.toNat < capacity.toNat) →
      ∃ x : BitVec 64, post.memory a = .word x ∧ x.toNat < capacity.toNat := by
    intro a n24 nb ⟨x,hx,xlt⟩
    rw [postMem,if_neg n24]
    rcases zm with same | ⟨ls,lslt,hz⟩
    · rw [same,yMem a nb]; exact ⟨x,hx,xlt⟩
    · rw [hz]
      split
      · exact ⟨dp,rfl,dpLt⟩
      · split
        · exact ⟨ls,rfl,lslt⟩
        · rw [yMem a nb]; exact ⟨x,hx,xlt⟩
  refine ⟨count - 1,by omega,?_,?_,postAddr,postBe,?_⟩
  · refine inv.recount (count - 1) ?_ (by rw [postMem,if_pos rfl]) ?_ postAddr postCode
    · intro k hk ne
      have tk := hdr k hk
      rw [postMem,if_neg (word_ne_of_toNat (by rw [tk,h24]; omega))]
      rcases zm with same | ⟨ls,lslt,hz⟩
      · rw [same,yMem _ (farByte _ (Or.inl (by rw [tk]; omega)))]
      · rw [hz,if_neg (word_ne_of_toNat (by rw [tk,(inv.slot_toNat ls lslt).2.2.1]; omega)),
          if_neg (word_ne_of_toNat (by rw [tk,(inv.slot_toNat dp dpLt).2.1]; omega)),
          yMem _ (farByte _ (Or.inl (by rw [tk]; omega)))]
    · rw [cm1,hashOccupiedCount_congr capacity (hashOccupancyRead post used) (hashOccupancyRead Y used) postReads]
      have := inv.agreement
      omega
  · constructor
    · intro q inside occupied
      have notHole : q ≠ I := by
        intro h; subst h; rw [postReads _ inside,yClear] at occupied; exact occupied rfl
      have xOcc : hashOccupancyRead X used q ≠ some 0 := by
        rw [← yReads q notHole,← postReads q inside]; exact occupied
      have qN := inv.slot_toNat q inside
      exact bounded _ (word_ne_of_toNat (by rw [qN.2.2.1,h24]; omega)) (farByte _ (Or.inr (by rw [qN.2.2.1]; omega)))
        (dd.orderPosOK q inside xOcc)
    · intro k inside
      rw [cm1] at inside
      have kN := inv.slot_toNat k (by omega)
      exact bounded _ (word_ne_of_toNat (by rw [kN.2.1,h24]; omega)) (farByte _ (Or.inr (by rw [kN.2.1]; omega)))
        (d.entries k (by omega))
  · intro w h
    have far : w.toNat < table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ w.toNat := h
    rw [postMem,if_neg (word_ne_of_toNat (by rw [h24]; omega))]
    have nb : w ≠ panByteAlignHOL (used + I) := farByte w (by omega)
    rcases zm with same | ⟨ls,lslt,hz⟩
    · rw [same,yMem w nb]; exact d.out w h
    · rw [hz,if_neg (word_ne_of_toNat (by rw [(inv.slot_toNat ls lslt).2.2.1]; omega)),
        if_neg (word_ne_of_toNat (by rw [(inv.slot_toNat dp dpLt).2.1]; omega)),yMem w nb]
      exact d.out w h

#print axioms htabDelTail_returnedE2

theorem htabDelLoopTail_returnedE2 {F : Type} {X post : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count empty : BitVec 64} {bits : Nat} {occ : BitVec 64 → Option UInt8} {M : BitVec 64 → HolWordLab 64} {I : BitVec 64} {v : ValueHOL 64}
    (run : evaluateHOLFiniteState X (.seq (.while (.const 1) htabDelBody) htabDelTail) = (some (.returned v),post))
    (d : DelStateE2 keyLength table keys stride capacity used values order orderPos count empty bits occ M X I I)
    (tL : X.locals.lookup (ofString "t") = some (.val (.word table)))
    (dp : BitVec 64) (dpL : X.locals.lookup (ofString "deleted_pos") = some (.val (.word dp)))
    (dpLt : dp.toNat < capacity.toNat)
    (budget : delLoopCost keyLength capacity + 0 ≤ X.clock) :
    ∃ count' : BitVec 64, count'.toNat + 1 = count.toNat ∧
      HtabAligned keyLength table keys stride capacity used values order orderPos count' bits post ∧
      OrderInv post capacity count' used order orderPos ∧ post.memaddrs = X.memaddrs ∧ post.be = X.be ∧
      OutsideSame post M table capacity orderPos := by
  have far := hashProbeDistance_lt_capacity capacity.toNat I.toNat empty.toNat d.d.iInside d.d.emptyInside
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases loopRun : evaluateHOLFiniteState X (.while (.const 1) htabDelBody) with
  | mk lr L =>
    rw [loopRun] at run
    cases lr with
    | some res =>
      exfalso
      obtain ⟨e,_⟩ := Prod.mk.inj run
      simp only [Option.some.injEq] at e
      subst e
      exact htabDelLoop_not_returned X L v loopRun
    | none =>
      simp only at run
      have loop := htabDelLoopE2_run keyLength table keys stride capacity used values order orderPos count empty bits occ M
        (capacity.toNat + 1) X d.d.inv.code ⟨I,I,d,fun _ => by omega,fun _ => by omega⟩
        (by unfold delLoopCost at budget; omega)
      rw [loopRun] at loop
      obtain ⟨_,_,_,exitFacts⟩ := loop
      obtain ⟨_,⟨I',J',dL,_,_⟩,_,_⟩ := exitFacts rfl
      have keptT := evaluate_avoidsLocal_flowing (ofString "t") (.while (.const 1) htabDelBody) (by decide) X
        (by rw [loopRun]; exact Or.inl rfl)
      have keptDp := evaluate_avoidsLocal_flowing (ofString "deleted_pos") (.while (.const 1) htabDelBody) (by decide) X
        (by rw [loopRun]; exact Or.inl rfl)
      have meta' := evaluateHOLFiniteState_metadata X (.while (.const 1) htabDelBody)
      rw [loopRun] at keptT keptDp meta'
      obtain ⟨c',h1,h2,h3,h4,h5,h6⟩ := htabDelTail_returnedE2 dL (by rw [keptT]; exact tL) dp (by rw [keptDp]; exact dpL) dpLt v run
      exact ⟨c',h1,h2,h3,h4.trans meta'.2.1,h5.trans meta'.2.2.1,h6⟩

#print axioms htabDelLoopTail_returnedE2

theorem htabDelAfterFind_returned_frame {F : Type} (r post : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count I : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits r)
    (tables : OrderInv r capacity count used order orderPos)
    (tableLocal : r.locals.lookup (ofString "t") = some (.val (.word table)))
    (indexLocal : r.locals.lookup (ofString "i") = some (.val (.word I)))
    (found : I = capacity ∨ (I.toNat < capacity.toNat ∧ hashOccupancyRead r used I ≠ some 0))
    (room : count.toNat < capacity.toNat)
    (budget : 0 + (delLoopCost keyLength capacity + 0) ≤ r.clock) (v : ValueHOL 64)
    (run : evaluateHOLFiniteState r htabDelAfterFind = (some (.returned v),post)) :
    ∃ count' : BitVec 64, (count' = count ∨ count'.toNat + 1 = count.toNat) ∧
      HtabAligned keyLength table keys stride capacity used values order orderPos count' bits post ∧
      OrderInv post capacity count' used order orderPos ∧ post.memaddrs = r.memaddrs ∧ post.be = r.be ∧
      (∀ w : BitVec 64, (w.toNat < table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ w.toNat) → post.memory w = r.memory w) := by
  obtain ⟨empty,emptyInside,emptyRead⟩ := hashOccupiedCount_exists_empty capacity (hashOccupancyRead r used)
    (by rw [← inv.agreement]; exact room)
  rw [htabDelAfterFind_shape] at run
  obtain ⟨vc,i0,ec,run0,m0,a0,b0,c0⟩ := dec_returned_state run
  rw [eval_header_load r _ table 16 capacity tableLocal (inv.header_domain 16 (by omega) (by omega)) inv.cell16] at ec
  cases ec
  rw [evaluateHOLFiniteState_seq_line780] at run0
  cases missingRun : evaluateHOLFiniteState (setVarHOLFinite (ofString "cap") (.val (.word capacity)) r) htabDelMissing with
  | mk mr mid =>
    rw [missingRun] at run0
    cases mr with
    | some res =>
      -- the missing-key return
      obtain ⟨_,rfl⟩ := Prod.mk.inj run0
      have frame := (memoryFrame_leaf _ htabDelMissing_readOnly (setVarHOLFinite (ofString "cap") (.val (.word capacity)) r)
        inv.code).1
      have meta' := evaluateHOLFiniteState_metadata (setVarHOLFinite (ofString "cap") (.val (.word capacity)) r) htabDelMissing
      rw [missingRun] at frame meta'
      refine ⟨count,Or.inl rfl,inv.transfer (m0.trans frame) (a0.trans meta'.2.1) (b0.trans meta'.2.2.1)
          (c0.trans meta'.1),tables.transfer (m0.trans frame) (a0.trans meta'.2.1) (b0.trans meta'.2.2.1),
        a0.trans meta'.2.1,b0.trans meta'.2.2.1,fun w _ => by rw [m0,frame]; rfl⟩
    | none =>
      simp only at run0
      obtain ⟨rfl,differs⟩ := htabDelMissing_normal _ mid I capacity
        (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,indexLocal])
        (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) missingRun
      obtain ⟨inside,occupied⟩ : I.toNat < capacity.toNat ∧ hashOccupancyRead r used I ≠ some 0 := by
        rcases found with same | h
        · exact absurd same differs
        · exact h
      rw [htabDelHeaders_shape] at run0
      obtain ⟨_,i1,e1,run1,m1,a1,b1,c1⟩ := dec_returned_state run0
      rw [eval_header_load _ _ table 0 keyLength (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
        (by exact inv.header_domain 0 (by omega) (by omega)) (by exact inv.cell0)] at e1
      cases e1
      obtain ⟨_,i2,e2,run2,m2,a2,b2,c2⟩ := dec_returned_state run1
      rw [eval_header_load _ _ table 8 stride (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
        (by exact inv.header_domain 8 (by omega) (by omega)) (by exact inv.cell8)] at e2
      cases e2
      obtain ⟨_,i3,e3,run3,m3,a3,b3,c3⟩ := dec_returned_state run2
      rw [eval_header_load _ _ table 32 keys (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
        (by exact inv.header_domain 32 (by omega) (by omega)) (by exact inv.cell32)] at e3
      cases e3
      obtain ⟨_,i4,e4,run4,m4,a4,b4,c4⟩ := dec_returned_state run3
      rw [eval_header_load _ _ table 40 values (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
        (by exact inv.header_domain 40 (by omega) (by omega)) (by exact inv.cell40)] at e4
      cases e4
      obtain ⟨_,i5,e5,run5,m5,a5,b5,c5⟩ := dec_returned_state run4
      rw [eval_header_load _ _ table 48 used (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
        (by exact inv.header_domain 48 (by omega) (by omega)) (by exact inv.cell48)] at e5
      cases e5
      obtain ⟨_,i6,e6,run6,m6,a6,b6,c6⟩ := dec_returned_state run5
      rw [eval_header_load _ _ table 56 order (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
        (by exact inv.header_domain 56 (by omega) (by omega)) (by exact inv.cell56)] at e6
      cases e6
      obtain ⟨_,i7,e7,run7,m7,a7,b7,c7⟩ := dec_returned_state run6
      rw [eval_header_load _ _ table 64 orderPos (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
        (by exact inv.header_domain 64 (by omega) (by omega)) (by exact inv.cell64)] at e7
      cases e7
      obtain ⟨_,i8,e8,run8,m8,a8,b8,c8⟩ := dec_returned_state run7
      obtain ⟨dp,hdp,dpLt⟩ := tables.1 I inside occupied
      have iN := inv.slot_toNat I inside
      have dpDomain : r.memaddrs (orderPos + I * 8) := by
        have := inv.headerKeys; have := inv.keysBefore; have := inv.usedBefore; have := inv.orderBefore
        have := inv.orderPosAligned
        exact inv.domain _ (by rw [iN.2.2.1]; omega) (by rw [iN.2.2.1]; omega) (by rw [iN.2.2.1]; omega)
      rw [eval_delLoad _ _ (orderPos + I * 8) dp (eval_delScaled8 _ _ _ orderPos I
          (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
          (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,indexLocal]))
        (by exact dpDomain) (by exact hdp)] at e8
      cases e8
      obtain ⟨_,i9,e9,run9,m9,a9,b9,c9⟩ := dec_returned_state run8
      rw [eval_delVar _ _ I
        (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,indexLocal])] at e9
      cases e9
      obtain ⟨c',h1,h2,h3,h4,h5,h6⟩ := htabDelLoopTail_returnedE2 (occ := fun q => hashOccupancyRead r used q) (empty := empty)
        (M := r.memory) run9
        { out := fun _ _ => rfl
          d := {
            inv := inv.transfer rfl rfl rfl rfl
            bytes := fun q _ => rfl
            emptyByte := emptyRead
            orderPosOK := tables.1
            capL := by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
            usedL := by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
            keysL := by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
            strideL := by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
            klenL := by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
            valsL := by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
            orderL := by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
            orderPosL := by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
            iL := by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,indexLocal]
            jL := by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
            emptyInside := emptyInside
            iInside := inside
            jInside := inside }
          holeOcc := occupied
          entries := tables.2 }
        (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
        dp (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) dpLt
        (by simp only [setVarHOLFinite]; omega)
      have pm := m0.trans (m1.trans (m2.trans (m3.trans (m4.trans (m5.trans (m6.trans (m7.trans (m8.trans m9))))))))
      have pa := a0.trans (a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans (a7.trans (a8.trans a9))))))))
      have pb := b0.trans (b1.trans (b2.trans (b3.trans (b4.trans (b5.trans (b6.trans (b7.trans (b8.trans b9))))))))
      have pc := c0.trans (c1.trans (c2.trans (c3.trans (c4.trans (c5.trans (c6.trans (c7.trans (c8.trans c9))))))))
      exact ⟨c',Or.inr h1,h2.transfer pm pa pb pc,h3.transfer pm pa pb,pa.trans h4,pb.trans h5,
        fun w h => by rw [pm]; exact h6 w h⟩

#print axioms htabDelAfterFind_returned_frame

/-- The returned deletion contract with the memory outside the table region unchanged. -/
theorem htabDel_returned_frame {F : Type} (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (keyLength table keys stride capacity used values order orderPos count key : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits state)
    (tables : OrderInv state capacity count used order orderPos)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (room : count.toNat < capacity.toNat) (small : keyLength.toNat ≤ 33806089496)
    (budget : delBodyCost keyLength capacity ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_del) = (some (.returned v),post)) :
    ∃ count' : BitVec 64, (count' = count ∨ count'.toNat + 1 = count.toNat) ∧
      HtabAligned keyLength table keys stride capacity used values order orderPos count' bits post ∧
      OrderInv post capacity count' used order orderPos ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ w : BitVec 64, (w.toNat < table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ w.toNat) → post.memory w = state.memory w) := by
  unfold delBodyCost at budget
  rw [source_htabDel_afterFind] at run
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
  obtain ⟨I,rfl,found⟩ := htabFindSlot_returned_occupied entry bodyPost table capacity used bits entryInv.power entryInv.code
    entryT (entryInv.header_domain 16 (by omega) (by omega)) entryInv.cell16
    (entryInv.header_domain 48 (by omega) (by omega)) entryInv.cell48 w bodyRun
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
      state.clock ≤ r.clock + (keyLength.toNat / 8 + 8 + 1 +
        (capacity.toNat * (4 * keyLength.toNat + 1 + 0 + 1) + 0)) + 1 :=
    ⟨rm.trans (frame.1.trans entryFacts.1),ra.trans (meta'.2.1.trans entryFacts.2.1),rb.trans (meta'.2.2.1.trans entryFacts.2.2.1),
      rc.trans (meta'.1.trans entryFacts.2.2.2.1),by rw [rclk fb2]; have := entryFacts.2.2.2.2.2; omega⟩
  have rInv := inv.transfer rFacts.1 rFacts.2.1 rFacts.2.2.1 rFacts.2.2.2.1
  have rTables := tables.transfer rFacts.1 rFacts.2.1 rFacts.2.2.1
  have rT := (ragree _ (by decide)).trans tableLocal
  have foundR : I = capacity ∨ (I.toNat < capacity.toNat ∧ hashOccupancyRead r used I ≠ some 0) := by
    have read : hashOccupancyRead r used I = hashOccupancyRead entry used I := by
      unfold hashOccupancyRead; rw [rFacts.1,rFacts.2.1,rFacts.2.2.1,entryFacts.1,entryFacts.2.1,entryFacts.2.2.1]
    rw [read]; exact found
  obtain ⟨c',shape,cInv,cTables,cAddr,cBe,cOut⟩ := htabDelAfterFind_returned_frame r inner keyLength table keys stride capacity used
    values order orderPos count I bits rInv rTables rT rh foundR room (by have := rFacts.2.2.2.2; omega) v rrun
  exact ⟨c',shape,cInv.transfer pm pa pb pc,cTables.transfer pm pa pb,pa.trans (cAddr.trans rFacts.2.1),
    pb.trans (cBe.trans rFacts.2.2.1),fun w h => by rw [pm,cOut w h,rFacts.1]⟩

#print axioms htabDel_returned_frame

/-- The discarded deletion call contract with the memory outside the table region unchanged. -/
theorem htabDel_call_normal_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (tableArgument keyArgument : ExpHOL 64)
    (keyLength table keys stride capacity used values order orderPos count key : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits state)
    (tables : OrderInv state capacity count used order orderPos)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [tableArgument,keyArgument] = some [.val (.word table),.val (.word key)])
    (room : count.toNat < capacity.toNat) (small : keyLength.toNat ≤ 33806089496)
    (budget : delBodyCost keyLength capacity + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_del") [tableArgument,keyArgument]) =
      (none,post)) :
    (∃ count' : BitVec 64, (count' = count ∨ count'.toNat + 1 = count.toNat) ∧
      HtabAligned keyLength table keys stride capacity used values order orderPos count' bits post ∧
      OrderInv post capacity count' used order orderPos) ∧
      post.locals = state.locals ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ w : BitVec 64, (w.toNat < table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ w.toNat) → post.memory w = state.memory w) := by
  obtain ⟨v,output,bodyRun,memory,locals⟩ := evaluate_discard_normal_body_memory state post (ofString "htab_del")
    _ _ _ _ .one args (htabDel_installed state table key inv.code) run
  obtain ⟨c',shape,outInv,outTables,outAddr,outBe,outOut⟩ := htabDel_returned_frame
    (callEntryStateHOLFinite state ((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update
      (ofString "key",.val (.word key)))) output v keyLength table keys stride capacity used values order orderPos count key bits
    (inv.transfer rfl rfl rfl rfl) (tables.transfer rfl rfl rfl)
    (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    room small (by change _ ≤ state.clock - 1; omega) bodyRun
  have meta' := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "htab_del") [tableArgument,keyArgument])
  rw [run] at meta'
  exact ⟨⟨c',shape,outInv.transfer memory (meta'.2.1.trans outAddr.symm) (meta'.2.2.1.trans outBe.symm)
    (meta'.1.trans (inv.code.trans outInv.code.symm)),
    outTables.transfer memory (meta'.2.1.trans outAddr.symm) (meta'.2.2.1.trans outBe.symm)⟩,locals,meta'.2.1,meta'.2.2.1,
    fun w h => by rw [memory,outOut w h]; rfl⟩

#print axioms htabDel_call_normal_frame

/-- The constructor contract with the memory below the old heap pointer unchanged. -/
theorem htabNew_returned_frame {F : Type} (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (keyLength capacity pointer : BitVec 64) (bits : Nat) (code : state.code = originalRuntimeCode)
    (keyLocal : state.locals.lookup (ofString "key_len") = some (.val (.word keyLength)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerAligned : pointer.toNat % 8 = 0) (pointerInside : pointer.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → pointer.toNat ≤ a.toNat → a.toNat < 33806089496 → state.memaddrs a)
    (power : capacity.toNat = 2 ^ bits) (small : keyLength.toNat ≤ 33806089496)
    (capSmall : capacity.toNat ≤ 33806089496)
    (keysSmall : capacity.toNat * (allocationEnd 0 keyLength).toNat ≤ 33806089496)
    (budget : capacity.toNat + 13 ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_new) = (some (.returned v),post)) :
    ∃ keys stride used values order orderPos : BitVec 64, v = .val (.word pointer) ∧
      HtabAligned keyLength pointer keys stride capacity used values order orderPos 0 bits post ∧
      OrderInv post capacity 0 used order orderPos ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      ∀ w : BitVec 64, w.toNat < pointer.toNat → post.memory w = state.memory w := by
  rw [source_htabNew_body] at run
  -- the header allocation
  obtain ⟨r1,i1,n1,o1,m1,a1,b1,c1,h1,q1,f1,k1,run1,pm1,pa1,pb1,pc1⟩ := alloc_decCall_returned state post _ (.const 72) _
    pointer 72 v rfl code heap (by omega) run
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
  have p1Facts := alloc_step_layout pointer 72 pointerInside q1
  have stride := allocationEnd_covers 0 keyLength (by change 0 + keyLength.toNat ≤ 33806089496; omega)
  change 0 + keyLength.toNat ≤ _ ∧ _ < 0 + keyLength.toNat + 8 ∧ _ % 8 = 0 at stride
  have hdr : ∀ k : Nat, k ≤ 72 → (pointer + BitVec.ofNat 64 k).toNat = pointer.toNat + k :=
    fun k hk => word_add_toNat pointer k (by omega)
  have keysSize : (capacity * allocationEnd 0 keyLength).toNat = capacity.toNat * (allocationEnd 0 keyLength).toNat :=
    BitVec.toNat_mul_of_lt (by omega)
  have eightSize : (capacity * 8).toNat = capacity.toNat * 8 := BitVec.toNat_mul_of_lt (by change _ * 8 < _; omega)
  -- keys
  obtain ⟨r3,i3,n3,o3,m3,a3,b3,c3,h3,q3,f3,k3,run7,pm3,pa3,pb3,pc3⟩ := alloc_decCall_returned W i2 _ _ _
    (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength) v
    (eval_mul_local_local W _ _ capacity _ (by rw [wL]; exact r2C) (by rw [wL]; exact r2S)) (wCo.trans code)
    (by rw [wG]; exact h1) (by rw [wK]; omega) run6
  have r3T : r3.locals.lookup (ofString "t") = some (.val (.word pointer)) := by rw [o3 _ (by decide),wL]; exact r2T
  have r3C : r3.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by rw [o3 _ (by decide),wL]; exact r2C
  have run8 := store_local_seq_returned r3 i3 _ 32 pointer (allocationEnd pointer 72) _ r3T (eval_delVar _ _ _ n3) run7
  generalize hX1 : sourceWriteWord r3 (pointer + 32) (allocationEnd pointer 72) = X1 at run8
  have x1F : X1.locals = r3.locals ∧ X1.memaddrs = state.memaddrs ∧ X1.be = state.be ∧ X1.code = state.code ∧
      X1.clock = r3.clock ∧ X1.globals = r3.globals ∧
      ∀ x, X1.memory x = if x = pointer + 32 then .word (allocationEnd pointer 72) else W.memory x := by
    rw [← hX1]; exact ⟨rfl,a3.trans wA,b3.trans wB,c3.trans wCo,rfl,rfl,fun x => by simp only [sourceWriteWord]; rw [m3]⟩
  obtain ⟨x1L,x1A,x1B,x1Co,x1K,x1G,x1M⟩ := x1F
  -- values
  obtain ⟨r4,i4,n4,o4,m4,a4,b4,c4,h4,q4,f4,k4,run9,pm4,pa4,pb4,pc4⟩ := alloc_decCall_returned X1 i3 _ _ _
    (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength)) (capacity * 8) v
    (eval_mul_local_const X1 _ capacity 8 (by rw [x1L]; exact r3C)) (x1Co.trans code)
    (by rw [x1G]; exact h3) (by rw [x1K]; omega) run8
  have r4T : r4.locals.lookup (ofString "t") = some (.val (.word pointer)) := by rw [o4 _ (by decide),x1L]; exact r3T
  have r4C : r4.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by rw [o4 _ (by decide),x1L]; exact r3C
  have run10 := store_local_seq_returned r4 i4 _ 40 pointer _ _ r4T (eval_delVar _ _ _ n4) run9
  generalize hX2 : sourceWriteWord r4 (pointer + 40) (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength)) = X2 at run10
  have x2F : X2.locals = r4.locals ∧ X2.memaddrs = state.memaddrs ∧ X2.be = state.be ∧ X2.code = state.code ∧
      X2.clock = r4.clock ∧ X2.globals = r4.globals ∧
      ∀ x, X2.memory x = if x = pointer + 40 then .word (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength))
        else X1.memory x := by
    rw [← hX2]; exact ⟨rfl,a4.trans x1A,b4.trans x1B,c4.trans x1Co,rfl,rfl,fun x => by simp only [sourceWriteWord]; rw [m4]⟩
  obtain ⟨x2L,x2A,x2B,x2Co,x2K,x2G,x2M⟩ := x2F
  have p2Facts := alloc_step_layout _ _ f1 q3
  have p3Facts := alloc_step_layout _ _ f3 q4
  generalize hS : allocationEnd 0 keyLength = Sd at *
  generalize hp1 : allocationEnd pointer 72 = p1 at *
  generalize hp2 : allocationEnd p1 (capacity * Sd) = p2 at *
  generalize hp3 : allocationEnd p2 (capacity * 8) = p3 at *
  -- the occupancy array and its zeroing
  obtain ⟨r5,i5,n5,o5,m5,a5,b5,c5,h5,q5,f5,k5,run11,pm5,pa5,pb5,pc5⟩ := alloc_decCall_returned X2 i4 _ _ _ p3 capacity v
    (eval_local_single X2 _ capacity (by rw [x2L]; exact r4C)) (x2Co.trans code) (by rw [x2G]; exact h4)
    (by rw [x2K]; omega) run10
  have p4Facts := alloc_step_layout _ _ f4 q5
  generalize hp4 : allocationEnd p3 capacity = p4 at *
  have r5T : r5.locals.lookup (ofString "t") = some (.val (.word pointer)) := by rw [o5 _ (by decide),x2L]; exact r4T
  have r5C : r5.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by rw [o5 _ (by decide),x2L]; exact r4C
  have zeroArgs : evalListHOLFinite r5 (h := fun a => Classical.propDecidable (r5.memaddrs a))
      [.var .local (ofString "used"),.var .local (ofString "cap")] = some [.val (.word p3),.val (.word capacity)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,n5,r5C]
  have r5Code : r5.code = originalRuntimeCode := (c5.trans x2Co).trans code
  obtain ⟨mz,zeroRun,_,zCost,_,zGl,_,zAddr,zBe,zLocals,zocc⟩ := evaluate_memzero_aligned_call_cells r5 _ _ p3 capacity zeroArgs
    r5Code (by omega) (by omega) p3Facts.2.1
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
    rw [(memzero_call_normal_memory r5 Z _ p3 capacity watched zeroArgs r5Code p3Facts.2.1 (by omega) outside zRun).1,m5]
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
  have x3H : X3.globals.lookup (ofString "heap_ptr") = some (.val (.word p4)) := by rw [x3G,zGl]; exact h5
  have x3T : X3.locals.lookup (ofString "t") = some (.val (.word pointer)) := by rw [x3L]; exact zT
  have x3C : X3.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by rw [x3L]; exact zC
  -- order
  obtain ⟨r6,i6,n6,o6,m6,a6,b6,c6,h6,q6,f6,k6,run14,pm6,pa6,pb6,pc6⟩ := alloc_decCall_returned X3 i5 _ _ _ p4 (capacity * 8) v
    (eval_mul_local_const X3 _ capacity 8 x3C) x3Co x3H (by rw [x3K]; omega) run13
  have p5Facts := alloc_step_layout _ _ f5 q6
  generalize hp5 : allocationEnd p4 (capacity * 8) = p5 at *
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
  obtain ⟨r7,i7,n7,o7,m7,a7,b7,c7,h7,q7,f7,k7,run16,pm7,pa7,pb7,pc7⟩ := alloc_decCall_returned X4 i6 _ _ _ p5 (capacity * 8) v
    (eval_mul_local_const X4 _ capacity 8 (by rw [x4L]; exact r6C)) x4Co (by rw [x4G]; exact h6) (by rw [x4K]; omega) run15
  have p6Facts := alloc_step_layout _ _ f6 q7
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
  rw [keysSize] at p2Facts
  rw [eightSize] at p3Facts p5Facts p6Facts
  obtain ⟨l1a,l1b,l1c⟩ := p1Facts
  obtain ⟨l2a,l2b,l2c⟩ := p2Facts
  obtain ⟨l3a,l3b,l3c⟩ := p3Facts
  obtain ⟨l4a,l4b,l4c⟩ := p4Facts
  obtain ⟨l5a,l5b,l5c⟩ := p5Facts
  obtain ⟨l6a,l6b,l6c⟩ := p6Facts
  have p1Facts : pointer.toNat + 72 ≤ p1.toNat ∧ p1.toNat % 8 = 0 := ⟨l1a,l1b⟩
  have p2Facts : p2.toNat % 8 = 0 := l2b
  have p3Facts : p3.toNat % 8 = 0 := l3b
  have p4Facts : p4.toNat % 8 = 0 := l4b
  have p5Facts : p5.toNat % 8 = 0 := l5b
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
  have inv : HtabAligned keyLength pointer p1 Sd capacity p3 p2 p4 p5 0 bits post := {
    code := postCode
    power := power
    tableAligned := pointerAligned
    keysAligned := p1Facts.2
    strideAligned := stride.2.2
    valuesAligned := p2Facts
    usedAligned := p3Facts
    orderAligned := p4Facts
    orderPosAligned := p5Facts
    headerKeys := p1Facts.1
    headerValues := by omega
    keysBefore := by omega
    valuesBefore := by omega
    usedBefore := by omega
    orderBefore := by omega
    endBound := by omega
    fits := by omega
    domain := fun a h1' h2' h3' => by rw [postAddr]; exact arena a h1' (by omega) (by omega)
    cell0 := by rw [postMem,x5M,if_neg (word_ne_of_toNat (by rw [t0,t64]; omega)),x4M,if_neg (word_ne_of_toNat (by rw [t0,t56]; omega)),x3M,if_neg (word_ne_of_toNat (by rw [t0,t48]; omega)),zFrame _ (Or.inl (by rw [t0]; omega)),x2M,if_neg (word_ne_of_toNat (by rw [t0,t40]; omega)),x1M,if_neg (word_ne_of_toNat (by rw [t0,t32]; omega)),wM,if_neg (word_ne_of_toNat (by rw [t0,t24]; omega)),if_neg (word_ne_of_toNat (by rw [t0,t16]; omega)),if_neg (word_ne_of_toNat (by rw [t0,t8]; omega)),if_pos rfl]
    cell8 := by rw [postMem,x5M,if_neg (word_ne_of_toNat (by rw [t8,t64]; omega)),x4M,if_neg (word_ne_of_toNat (by rw [t8,t56]; omega)),x3M,if_neg (word_ne_of_toNat (by rw [t8,t48]; omega)),zFrame _ (Or.inl (by rw [t8]; omega)),x2M,if_neg (word_ne_of_toNat (by rw [t8,t40]; omega)),x1M,if_neg (word_ne_of_toNat (by rw [t8,t32]; omega)),wM,if_neg (word_ne_of_toNat (by rw [t8,t24]; omega)),if_neg (word_ne_of_toNat (by rw [t8,t16]; omega)),if_pos rfl]
    cell16 := by rw [postMem,x5M,if_neg (word_ne_of_toNat (by rw [t16,t64]; omega)),x4M,if_neg (word_ne_of_toNat (by rw [t16,t56]; omega)),x3M,if_neg (word_ne_of_toNat (by rw [t16,t48]; omega)),zFrame _ (Or.inl (by rw [t16]; omega)),x2M,if_neg (word_ne_of_toNat (by rw [t16,t40]; omega)),x1M,if_neg (word_ne_of_toNat (by rw [t16,t32]; omega)),wM,if_neg (word_ne_of_toNat (by rw [t16,t24]; omega)),if_pos rfl]
    cell24 := by rw [postMem,x5M,if_neg (word_ne_of_toNat (by rw [t24,t64]; omega)),x4M,if_neg (word_ne_of_toNat (by rw [t24,t56]; omega)),x3M,if_neg (word_ne_of_toNat (by rw [t24,t48]; omega)),zFrame _ (Or.inl (by rw [t24]; omega)),x2M,if_neg (word_ne_of_toNat (by rw [t24,t40]; omega)),x1M,if_neg (word_ne_of_toNat (by rw [t24,t32]; omega)),wM,if_pos rfl]
    cell32 := by rw [postMem,x5M,if_neg (word_ne_of_toNat (by rw [t32,t64]; omega)),x4M,if_neg (word_ne_of_toNat (by rw [t32,t56]; omega)),x3M,if_neg (word_ne_of_toNat (by rw [t32,t48]; omega)),zFrame _ (Or.inl (by rw [t32]; omega)),x2M,if_neg (word_ne_of_toNat (by rw [t32,t40]; omega)),x1M,if_pos rfl]
    cell40 := by rw [postMem,x5M,if_neg (word_ne_of_toNat (by rw [t40,t64]; omega)),x4M,if_neg (word_ne_of_toNat (by rw [t40,t56]; omega)),x3M,if_neg (word_ne_of_toNat (by rw [t40,t48]; omega)),zFrame _ (Or.inl (by rw [t40]; omega)),x2M,if_pos rfl]
    cell48 := by rw [postMem,x5M,if_neg (word_ne_of_toNat (by rw [t48,t64]; omega)),x4M,if_neg (word_ne_of_toNat (by rw [t48,t56]; omega)),x3M,if_pos rfl]
    cell56 := by rw [postMem,x5M,if_neg (word_ne_of_toNat (by rw [t56,t64]; omega)),x4M,if_pos rfl]
    cell64 := by rw [postMem,x5M,if_pos rfl]
    agreement := by rw [hashOccupiedCount_congr capacity _ _ reads,zocc]; rfl }
  refine ⟨p1,Sd,p3,p2,p4,p5,value,inv,OrderInv.of_count_zero inv,postAddr,postBe,fun w below => ?_⟩
  have nk : ∀ k : Nat, k ≤ 64 → (pointer + BitVec.ofNat 64 k).toNat = pointer.toNat + k := fun k hk => hdr k (by omega)
  rw [postMem,x5M,if_neg (word_ne_of_toNat (by rw [t64]; omega)),x4M,if_neg (word_ne_of_toNat (by rw [t56]; omega)),
    x3M,if_neg (word_ne_of_toNat (by rw [t48]; omega)),zFrame w (Or.inl (by omega)),x2M,
    if_neg (word_ne_of_toNat (by rw [t40]; omega)),x1M,if_neg (word_ne_of_toNat (by rw [t32]; omega)),wM,
    if_neg (word_ne_of_toNat (by rw [t24]; omega)),if_neg (word_ne_of_toNat (by rw [t16]; omega)),
    if_neg (word_ne_of_toNat (by rw [t8]; omega)),if_neg (word_ne_of_toNat (by rw [t0]; omega))]

#print axioms htabNew_returned_frame
end InitECandidate.Runtime
