import InitECandidate.Runtime.HtabOutsideFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The constructor contract for every key length below 2^28 and every
power-of-two capacity: capacity and key-array size bounds come from the actual
returned allocations, and the memory below the old heap pointer is kept. -/
theorem htabNew_returned_canonical {F : Type} (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (keyLength capacity pointer : BitVec 64) (bits : Nat) (code : state.code = originalRuntimeCode)
    (keyLocal : state.locals.lookup (ofString "key_len") = some (.val (.word keyLength)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerAligned : pointer.toNat % 8 = 0) (pointerInside : pointer.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → pointer.toNat ≤ a.toNat → a.toNat < 33806089496 → state.memaddrs a)
    (power : capacity.toNat = 2 ^ bits) (klenSmall : keyLength.toNat < 2 ^ 28)
    (budget : capacity.toNat + 13 ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_new) = (some (.returned v),post)) :
    ∃ keys stride used values order orderPos : BitVec 64, v = .val (.word pointer) ∧
      HtabAligned keyLength pointer keys stride capacity used values order orderPos 0 bits post ∧
      OrderInv post capacity 0 used order orderPos ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      ∀ w : BitVec 64, w.toNat < pointer.toNat → post.memory w = state.memory w := by
  have small : keyLength.toNat ≤ 33806089496 := by omega
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
  have capSmall : capacity.toNat ≤ 33806089496 := by have := p4Facts.2.2; omega
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
  rw [postMem,x5M,if_neg (word_ne_of_toNat (by rw [t64]; omega)),x4M,if_neg (word_ne_of_toNat (by rw [t56]; omega)),
    x3M,if_neg (word_ne_of_toNat (by rw [t48]; omega)),zFrame w (Or.inl (by omega)),x2M,
    if_neg (word_ne_of_toNat (by rw [t40]; omega)),x1M,if_neg (word_ne_of_toNat (by rw [t32]; omega)),wM,
    if_neg (word_ne_of_toNat (by rw [t24]; omega)),if_neg (word_ne_of_toNat (by rw [t16]; omega)),
    if_neg (word_ne_of_toNat (by rw [t8]; omega)),if_neg (word_ne_of_toNat (by rw [t0]; omega))]

#print axioms htabNew_returned_canonical

/-- The canonical constructor contract from an actual call entry on word arguments. -/
theorem htabNew_entry_canonical {F : Type} (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (keyLength capacity pointer : BitVec 64) (bits : Nat) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerAligned : pointer.toNat % 8 = 0) (pointerInside : pointer.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → pointer.toNat ≤ a.toNat → a.toNat < 33806089496 → state.memaddrs a)
    (power : capacity.toNat = 2 ^ bits) (klenSmall : keyLength.toNat < 2 ^ 28)
    (budget : capacity.toNat + 14 ≤ state.clock)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite state
      ((HolFiniteMapExact.empty.update (ofString "key_len",.val (.word keyLength))).update (ofString "cap",.val (.word capacity))))
      (sourceFunctionBody Guest.guestFn_htab_new) = (some (.returned v),post)) :
    ∃ keys stride used values order orderPos : BitVec 64, v = .val (.word pointer) ∧
      HtabAligned keyLength pointer keys stride capacity used values order orderPos 0 bits post ∧
      OrderInv post capacity 0 used order orderPos ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      ∀ w : BitVec 64, w.toNat < pointer.toNat → post.memory w = state.memory w :=
  htabNew_returned_canonical (callEntryStateHOLFinite state
      ((HolFiniteMapExact.empty.update (ofString "key_len",.val (.word keyLength))).update (ofString "cap",.val (.word capacity))))
    post v keyLength capacity pointer bits (by exact code)
    (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) (by exact heap) pointerAligned pointerInside
    (fun a h1 h2 h3 => by exact arena a h1 h2 h3) power klenSmall
    (by change _ ≤ state.clock - 1; omega) run
#print axioms htabNew_entry_canonical
end InitECandidate.Runtime
