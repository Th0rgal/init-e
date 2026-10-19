import InitECandidate.Runtime.StateInitJournalSource
import InitECandidate.Runtime.HtabNewTop
import InitECandidate.Runtime.HtabUnionSites
import InitECandidate.Runtime.HashNewLocalCallBeforeHeader
import InitECandidate.Runtime.HashNewHeapDomains
import InitECandidate.Runtime.FrameHalt
import InitECandidate.Runtime.HashNewHeaderHeap
import InitECandidate.Runtime.StateFreshTxPlan
import InitECandidate.Runtime.HtabTxOuter
import InitECandidate.Runtime.AllocationGlobalCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def blockPointerStore (offset : Nat) : ProgHOL 64 :=
  .store (.op .add [.var .global (ofString "bs"),.const (BitVec.ofNat 64 offset)]) (.var .local (ofString "t"))

def blockCtorSeq : List (Nat × Nat × Nat) → ProgHOL 64 → ProgHOL 64
  | [], tail => tail
  | (width,capacity,offset) :: rest, tail =>
    .seq (.call (some (some (.local,ofString "t"),none)) (ofString "htab_new")
      [.const (BitVec.ofNat 64 width),.const (BitVec.ofNat 64 capacity)])
      (.seq (blockPointerStore offset) (blockCtorSeq rest tail))

def blockTablesFirst : List (Nat × Nat × Nat) := [(20,256,8),(20,256,16),(52,256,24),(20,64,32),(52,64,40),(32,64,48)]

def blockTablesLast : List (Nat × Nat × Nat) := [(20,256,72)]

def blockSegment (tail : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (some (.global,ofString "bs"),none)) (ofString "alloc") [.const 80])
    (.seq (.store (.op .add [.var .global (ofString "bs"),.const 0]) (.var .global (ofString "ws")))
      (blockCtorSeq blockTablesFirst
        (.seq (.store (.op .add [.var .global (ofString "bs"),.const 56]) (.const 0))
          (.seq (.store (.op .add [.var .global (ofString "bs"),.const 64]) (.const 0))
            (blockCtorSeq blockTablesLast tail)))))

theorem source_stateInit_block :
    stateInitSpineDrop 8 (sourceFunctionBody Guest.guestFn_state_init) =
      blockSegment (stateInitSpineDrop 26 (sourceFunctionBody Guest.guestFn_state_init)) := by
  unfold sourceFunctionBody
  rw [declToHOL_eq]
  rfl

#print axioms source_stateInit_block

set_option maxHeartbeats 4000000 in
/-- `htabNew_returned_top` with the keys array before the values array. -/
theorem htabNew_returned_topV {F : Type} (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
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
      keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat ∧
      OrderInv post capacity 0 used order orderPos ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ w : BitVec 64, w.toNat < pointer.toNat → post.memory w = state.memory w) ∧
      ∃ p : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) ∧
        orderPos.toNat + capacity.toNat * 8 ≤ p.toNat ∧ p.toNat % 8 = 0 ∧ p.toNat ≤ 33806089496 := by
  have small : keyLength.toNat ≤ 33806089496 := by omega
  rw [source_htabNew_body] at run
  -- the header allocation
  obtain ⟨r1,i1,n1,o1,m1,a1,b1,c1,h1,q1,f1,k1,run1,pm1,pa1,pb1,pc1,pg1⟩ := alloc_decCall_returnedG state post _ (.const 72) _
    pointer 72 v rfl code heap (by omega) run
  obtain ⟨sv,i2,se,run2,m2,a2,b2,c2,g2⟩ := dec_returned_globals run1
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
  obtain ⟨r3,i3,n3,o3,m3,a3,b3,c3,h3,q3,f3,k3,run7,pm3,pa3,pb3,pc3,pg3⟩ := alloc_decCall_returnedG W i2 _ _ _
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
  obtain ⟨r4,i4,n4,o4,m4,a4,b4,c4,h4,q4,f4,k4,run9,pm4,pa4,pb4,pc4,pg4⟩ := alloc_decCall_returnedG X1 i3 _ _ _
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
  obtain ⟨r5,i5,n5,o5,m5,a5,b5,c5,h5,q5,f5,k5,run11,pm5,pa5,pb5,pc5,pg5⟩ := alloc_decCall_returnedG X2 i4 _ _ _ p3 capacity v
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
  obtain ⟨r6,i6,n6,o6,m6,a6,b6,c6,h6,q6,f6,k6,run14,pm6,pa6,pb6,pc6,pg6⟩ := alloc_decCall_returnedG X3 i5 _ _ _ p4 (capacity * 8) v
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
  obtain ⟨r7,i7,n7,o7,m7,a7,b7,c7,h7,q7,f7,k7,run16,pm7,pa7,pb7,pc7,pg7⟩ := alloc_decCall_returnedG X4 i6 _ _ _ p5 (capacity * 8) v
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
  have retG := return_local_globals X5 i7 _ v run17
  refine ⟨p1,Sd,p3,p2,p4,p5,value,inv,by omega,OrderInv.of_count_zero inv,postAddr,postBe,fun w below => ?_,
    allocationEnd p5 (capacity * 8),?_,l6a,l6b,f7⟩
  swap
  · rw [pg1,g2,pg3,pg4,pg5,pg6,pg7,retG]
    rw [← hX5]
    exact h7
  rw [postMem,x5M,if_neg (word_ne_of_toNat (by rw [t64]; omega)),x4M,if_neg (word_ne_of_toNat (by rw [t56]; omega)),
    x3M,if_neg (word_ne_of_toNat (by rw [t48]; omega)),zFrame w (Or.inl (by omega)),x2M,
    if_neg (word_ne_of_toNat (by rw [t40]; omega)),x1M,if_neg (word_ne_of_toNat (by rw [t32]; omega)),wM,
    if_neg (word_ne_of_toNat (by rw [t24]; omega)),if_neg (word_ne_of_toNat (by rw [t16]; omega)),
    if_neg (word_ne_of_toNat (by rw [t8]; omega)),if_neg (word_ne_of_toNat (by rw [t0]; omega))]

#print axioms htabNew_returned_topV

/-- `binner = htab_new(32, 8)`-style call: a fresh aligned table at the old heap pointer, count 0, its arrays
ending at or below the new heap pointer, memory below the old heap pointer kept; keys array before values. -/
theorem htabNew_call_assignV {F : Type} (state post : PanSemStateFiniteExact 64 F) (name : MlS)
    (keyLength capacity pointer : BitVec 64) (bits : Nat) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerAligned : pointer.toNat % 8 = 0) (pointerInside : pointer.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → pointer.toNat ≤ a.toNat → a.toNat < 33806089496 → state.memaddrs a)
    (power : capacity.toNat = 2 ^ bits) (klenSmall : keyLength.toNat < 2 ^ 28)
    (budget : capacity.toNat + 14 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (some (.local,name),none)) (ofString "htab_new")
      [.const keyLength,.const capacity]) = (none,post)) :
    ∃ keys stride used values order orderPos : BitVec 64,
      HtabAligned keyLength pointer keys stride capacity used values order orderPos 0 bits post ∧
      keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat ∧
      OrderInv post capacity 0 used order orderPos ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      post.locals.lookup name = some (.val (.word pointer)) ∧
      (∀ k, k ≠ name → post.locals.lookup k = state.locals.lookup k) ∧
      (∀ w : BitVec 64, w.toNat < pointer.toNat → post.memory w = state.memory w) ∧
      (∃ p : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) ∧
        orderPos.toNat + capacity.toNat * 8 ≤ p.toNat ∧ p.toNat % 8 = 0 ∧ p.toNat ≤ 33806089496) ∧
      HeapRel state.globals post.globals := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.const keyLength,.const capacity] = some [.val (.word keyLength),.val (.word capacity)] := by
    rw [evalListHOLFinite_eq_toExact]; rfl
  obtain ⟨value,output,bodyRun,pm,pg,pa,pb,pc,pl,po⟩ := assign_call_normal state post name _ _ _ _ _ _ args
    (htabNew_installed state keyLength capacity code) run
  obtain ⟨keys,stride,used,values,order,orderPos,rfl,inv,kv,tables,oa,ob,frame,p,hp,le,pal,pin⟩ := htabNew_returned_topV
    (callEntryStateHOLFinite state ((HolFiniteMapExact.empty.update (ofString "key_len",.val (.word keyLength))).update
      (ofString "cap",.val (.word capacity)))) output _ keyLength capacity pointer bits (by exact code)
    (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) (by exact heap) pointerAligned pointerInside
    (fun a h1 h2 h3 => by exact arena a h1 h2 h3) power klenSmall (by change _ ≤ state.clock - 1; omega) bodyRun
  have rel := normalRel_apply (htabNew_normalRel) (X := callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "key_len",.val (.word keyLength))).update (ofString "cap",.val (.word capacity))))
    (by rw [bodyRun]; exact Or.inr (Or.inr (Or.inr ⟨_,rfl⟩))) (by exact code)
  rw [bodyRun] at rel
  refine ⟨keys,stride,used,values,order,orderPos,inv.transfer pm pa pb pc,kv,tables.transfer pm pa pb,pa.trans oa,pb.trans ob,
    pl,po,fun w below => by rw [pm]; exact frame w below,⟨p,by rw [pg]; exact hp,le,pal,pin⟩,by rw [pg]; exact rel⟩

#print axioms htabNew_call_assignV

set_option maxHeartbeats 2000000 in
/-- One block-table constructor step `t = htab_new(w, c); st bs + o, t` from an aligned heap pointer with the
full heap domain: the new table is an aligned empty table at the old heap pointer with the order invariant, its
pointer is stored at `bs + o` (below the old heap pointer), and every other word below the old heap pointer is
kept. -/
theorem block_ctor_step {F : Type} (s : PanSemStateFiniteExact 64 F) (B p : BitVec 64) (w c o bits : Nat)
    (rest : ProgHOL 64) (code : s.code = originalRuntimeCode)
    (hB : s.globals.lookup (ofString "bs") = some (.val (.word B)))
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p))) (pal : p.toNat % 8 = 0)
    (domain : ∀ a : BitVec 64, a.toNat < 33806089496 → s.memaddrs a)
    (wB : w ≤ 52) (cB : c < 2 ^ 64) (power : c = 2 ^ bits)
    (space : p.toNat + 81 * c + 114 ≤ 33806089496) (ticks : c + 14 ≤ s.clock)
    (oldT : BitVec 64) (tL : s.locals.lookup (ofString "t") = some (.val (.word oldT)))
    (oBelow : (B + BitVec.ofNat 64 o).toNat < p.toNat) :
    ∃ (r : PanSemStateFiniteExact 64 F) (keys stride used values order orderPos p' : BitVec 64),
      evaluateHOLFiniteState s (.seq (.call (some (some (.local,ofString "t"),none)) (ofString "htab_new")
        [.const (BitVec.ofNat 64 w),.const (BitVec.ofNat 64 c)]) (.seq (blockPointerStore o) rest)) =
        evaluateHOLFiniteState r rest ∧
      HtabAligned (BitVec.ofNat 64 w) p keys stride (BitVec.ofNat 64 c) used values order orderPos 0 bits r ∧
      keys.toNat + (BitVec.ofNat 64 c).toNat * stride.toNat ≤ values.toNat ∧
      OrderInv r (BitVec.ofNat 64 c) 0 used order orderPos ∧
      r.memory (B + BitVec.ofNat 64 o) = .word p ∧
      (∀ a : BitVec 64, a.toNat < p.toNat → a ≠ B + BitVec.ofNat 64 o → r.memory a = s.memory a) ∧
      r.code = s.code ∧ r.memaddrs = s.memaddrs ∧ r.be = s.be ∧ HeapRel s.globals r.globals ∧
      r.globals.lookup (ofString "heap_ptr") = some (.val (.word p')) ∧
      orderPos.toNat + c * 8 ≤ p'.toNat ∧ p'.toNat % 8 = 0 ∧ p'.toNat ≤ 33806089496 ∧
      p' = stateFreshTxNextTable p w c ∧
      r.locals.lookup (ofString "t") = some (.val (.word p)) ∧ s.clock ≤ r.clock + (c + 14) ∧ r.clock ≤ s.clock := by
  have cN : (BitVec.ofNat 64 c).toNat = c := Nat.mod_eq_of_lt cB
  have wN : (BitVec.ofNat 64 w).toNat = w := Nat.mod_eq_of_lt (by omega)
  obtain ⟨_,hdrD,wordD,byteD⟩ := htabNew_heap_domains s p (BitVec.ofNat 64 w) (BitVec.ofNat 64 c) (by omega)
    (by rw [cN]; exact space) domain
  obtain ⟨post,run,clk1,clk2,_⟩ := evaluate_htabNew_local_call_before_header s (.const (BitVec.ofNat 64 w))
    (.const (BitVec.ofNat 64 c)) p (BitVec.ofNat 64 w) (BitVec.ofNat 64 c) (by rw [evalListHOLFinite_eq_toExact]; rfl)
    code (by rw [cN]; omega) heap (by omega) pal (by rw [cN]; exact space) hdrD wordD byteD (ofString "t") oldT tL
  obtain ⟨keys,stride,used,values,order,orderPos,inv,kv,tables,ma,mb,tl,_,frame,⟨p',hp',le',al',in'⟩,rel⟩ :=
    htabNew_call_assignV s post (ofString "t") (BitVec.ofNat 64 w) (BitVec.ofNat 64 c) p bits code heap pal (by omega)
      (fun a _ _ h3 => domain a h3) (by rw [cN]; exact power) (by rw [wN]; omega) (by rw [cN]; omega) run
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const (BitVec.ofNat 64 w),.const (BitVec.ofNat 64 c)] =
        some [.val (.word (BitVec.ofNat 64 w)),.val (.word (BitVec.ofNat 64 c))] := by
    rw [evalListHOLFinite_eq_toExact]; rfl
  obtain ⟨_,output,bodyRun,_,pg,_,_,_,_,_⟩ := assign_call_normal s post (ofString "t") _ _ _ _ _ _ args
    (htabNew_installed s (BitVec.ofNat 64 w) (BitVec.ofNat 64 c) code) run
  obtain ⟨post0,body0,_,_,_,_,_,_,heap0,_⟩ := evaluate_source_htabNew_header_heap
    (callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (ofString "key_len",.val (.word (BitVec.ofNat 64 w)))).update
      (ofString "cap",.val (.word (BitVec.ofNat 64 c))))) p (BitVec.ofNat 64 w) (BitVec.ofNat 64 c) (by exact code)
    (by change _ ≤ s.clock - 1; rw [cN]; omega) (by exact heap) (by omega) pal (by rw [cN]; exact space)
    (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) (by exact hdrD) (by exact wordD)
    (by exact byteD)
  rw [bodyRun] at body0
  obtain ⟨_,rfl⟩ := Prod.mk.inj body0
  have heapNext : post.globals.lookup (ofString "heap_ptr") = some (.val (.word (stateFreshTxNextTable p w c))) := by
    rw [pg]; exact heap0
  have pEq : p' = stateFreshTxNextTable p w c := by
    rw [heapNext] at hp'
    simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at hp'
    exact hp'.symm
  have pc : post.code = s.code := by
    have := evaluateHOLFiniteState_metadata s (.call (some (some (.local,ofString "t"),none)) (ofString "htab_new")
      [.const (BitVec.ofNat 64 w),.const (BitVec.ofNat 64 c)])
    rw [run] at this; exact this.1
  have hB' : post.globals.lookup (ofString "bs") = some (.val (.word B)) := by rw [rel.1 _ (by decide)]; exact hB
  have store := evaluate_store_word post (B + BitVec.ofNat 64 o) p
    (.op .add [.var .global (ofString "bs"),.const (BitVec.ofNat 64 o)]) (.var .local (ofString "t"))
    (eval_add2 post _ _ _ _ (eval_global_word post _ B hB') (item_eval_const post _)) (item_eval_locals post _ p tl)
    (by rw [ma]; exact domain _ (by omega))
  let r := sourceWriteWord post (B + BitVec.ofNat 64 o) p
  have rmem : ∀ a, a ≠ B + BitVec.ofNat 64 o → r.memory a = post.memory a := by
    intro a h; simp only [r,sourceWriteWord,if_neg h]
  have hk := inv.headerKeys; have kb := inv.keysBefore; have ub := inv.usedBefore; have ob := inv.orderBefore
  have keep : ∀ x : BitVec 64, HtabFoot p (BitVec.ofNat 64 c) used order orderPos x.toNat → r.memory x = post.memory x := by
    intro x h
    apply rmem
    intro e
    unfold HtabFoot at h
    rw [e] at h
    have : keys.toNat ≤ keys.toNat + (BitVec.ofNat 64 c).toNat * stride.toNat := Nat.le_add_right _ _
    omega
  have K := inv.toRegions.foot_keep (r := r) keep
  refine ⟨r,keys,stride,used,values,order,orderPos,p',?_,inv.congr rfl rfl rfl K.1 K.2.1,kv,
    tables.congr inv.toRegions.count_le rfl rfl K.2.1 K.2.2.1 K.2.2.2,by simp [r,sourceWriteWord],
    fun a lt ne => by rw [rmem a ne]; exact frame a lt,pc,ma,mb,rel,hp',by rw [cN] at le'; exact le',al',in',pEq,tl,
    by change s.clock ≤ post.clock + (c + 14); omega,clk2⟩
  rw [evaluateHOLFiniteState_seq_line780,run]
  dsimp only
  unfold blockPointerStore
  rw [evaluateHOLFiniteState_seq_line780,store]

#print axioms block_ctor_step

/-- An aligned table with the order invariant survives any step that keeps its block `[table, orderPos + cap * 8)`. -/
theorem HtabAligned.keep_block {F G : Type} {s : PanSemStateFiniteExact 64 F} {r : PanSemStateFiniteExact 64 G}
    {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat}
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits s)
    (tables : OrderInv s capacity count used order orderPos)
    (memaddrs : r.memaddrs = s.memaddrs) (be : r.be = s.be) (code : r.code = s.code)
    (keep : ∀ a : BitVec 64, table.toNat ≤ a.toNat → a.toNat < orderPos.toNat + capacity.toNat * 8 →
      r.memory a = s.memory a) :
    HtabAligned keyLength table keys stride capacity used values order orderPos count bits r ∧
      OrderInv r capacity count used order orderPos := by
  have hk := inv.headerKeys; have kb := inv.keysBefore; have ub := inv.usedBefore; have ob := inv.orderBefore
  have K := inv.toRegions.foot_keep (r := r) (fun x h => keep x (by
    have : keys.toNat ≤ keys.toNat + capacity.toNat * stride.toNat := Nat.le_add_right _ _
    unfold HtabFoot at h; omega) (inv.foot_below x.toNat h))
  exact ⟨inv.congr memaddrs be code K.1 K.2.1,tables.congr inv.toRegions.count_le memaddrs be K.2.1 K.2.2.1 K.2.2.2⟩

/-- Constructor plan for block tables: width, capacity (a power of two) and record offset (inside the 80-byte
record, all distinct). -/
def BlockPlan : List (Nat × Nat × Nat) → Prop
  | [] => True
  | (w,c,o) :: rest => w ≤ 52 ∧ c < 2 ^ 64 ∧ (∃ bits, c = 2 ^ bits) ∧ o + 8 ≤ 80 ∧
      o ∉ rest.map (fun x => x.2.2) ∧ BlockPlan rest

theorem BlockPlan.cons {w c o : Nat} {rest : List (Nat × Nat × Nat)} (bits : Nat) (wB : w ≤ 52) (cB : c < 2 ^ 64)
    (power : c = 2 ^ bits) (oB : o + 8 ≤ 80) (fresh : o ∉ rest.map (fun x => x.2.2)) (plan : BlockPlan rest) :
    BlockPlan ((w,c,o) :: rest) := ⟨wB,cB,⟨bits,power⟩,oB,fresh,plan⟩

theorem BlockPlan.offsets : ∀ (specs : List (Nat × Nat × Nat)), BlockPlan specs →
    ∀ o ∈ specs.map (fun x => x.2.2), o + 8 ≤ 80
  | [], _, _, m => by simp at m
  | (w,c,o) :: rest, ⟨_,_,_,oB,_,plan⟩, o', m => by
    rcases List.mem_cons.mp m with e | m
    · rw [e]; exact oB
    · exact BlockPlan.offsets rest plan o' m

def blockClock : List (Nat × Nat × Nat) → Nat
  | [] => 0
  | (_,c,_) :: rest => c + 14 + blockClock rest

/-- The built block tables, laid out in constructor order from `lo` up to `hi`: each record cell `bs + o` holds
an aligned empty table with the order invariant, whose block ends before the next table. -/
def BlockBuilt {F : Type} (B : BitVec 64) : List (Nat × Nat × Nat) → PanSemStateFiniteExact 64 F → Nat → Nat → Prop
  | [], _, lo, hi => lo ≤ hi
  | (w,c,o) :: rest, s, lo, hi => ∃ (t keys stride used values order orderPos : BitVec 64) (bits mid : Nat),
      lo ≤ t.toNat ∧ c = 2 ^ bits ∧ s.memory (B + BitVec.ofNat 64 o) = .word t ∧
      HtabAligned (BitVec.ofNat 64 w) t keys stride (BitVec.ofNat 64 c) used values order orderPos 0 bits s ∧
      keys.toNat + (BitVec.ofNat 64 c).toNat * stride.toNat ≤ values.toNat ∧
      OrderInv s (BitVec.ofNat 64 c) 0 used order orderPos ∧
      orderPos.toNat + (BitVec.ofNat 64 c).toNat * 8 ≤ mid ∧ BlockBuilt B rest s mid hi

theorem BlockBuilt.le {F : Type} {B : BitVec 64} :
    ∀ (specs : List (Nat × Nat × Nat)) (s : PanSemStateFiniteExact 64 F) (lo hi : Nat), BlockBuilt B specs s lo hi → lo ≤ hi
  | [], _, _, _, h => h
  | (_,_,_) :: rest, s, lo, hi, ⟨t,_,_,_,_,_,orderPos,_,mid,l1,_,_,inv,_,_,l2,h⟩ => by
    have := BlockBuilt.le rest s mid hi h
    have := inv.headerKeys; have := inv.keysBefore; have := inv.usedBefore; have := inv.orderBefore
    omega

/-- The built tables survive any step keeping `[lo, hi)` and the record cells. -/
theorem BlockBuilt.keep {F G : Type} {B : BitVec 64} :
    ∀ (specs : List (Nat × Nat × Nat)) (s : PanSemStateFiniteExact 64 F) (r : PanSemStateFiniteExact 64 G) (lo hi : Nat),
    BlockBuilt B specs s lo hi → r.memaddrs = s.memaddrs → r.be = s.be → r.code = s.code →
    (∀ a : BitVec 64, lo ≤ a.toNat → a.toNat < hi → r.memory a = s.memory a) →
    (∀ o ∈ specs.map (fun x => x.2.2), r.memory (B + BitVec.ofNat 64 o) = s.memory (B + BitVec.ofNat 64 o)) →
    BlockBuilt B specs r lo hi
  | [], _, _, _, _, h, _, _, _, _, _ => h
  | (w,c,o) :: rest, s, r, lo, hi, ⟨t,keys,stride,used,values,order,orderPos,bits,mid,l1,pw,cell,inv,kv,tables,l2,h⟩,
      ma, mb, mc, keep, cells => by
    have midHi := BlockBuilt.le rest s mid hi h
    obtain ⟨inv',tables'⟩ := inv.keep_block tables ma mb mc (fun a h1 h2 => keep a (by omega) (by omega))
    exact ⟨t,keys,stride,used,values,order,orderPos,bits,mid,l1,pw,by rw [cells o (List.mem_cons_self ..)]; exact cell,
      inv',kv,tables',l2,BlockBuilt.keep rest s r mid hi h ma mb mc (fun a h1 h2 => keep a (by
        have := inv.headerKeys; have := inv.keysBefore; have := inv.usedBefore; have := inv.orderBefore
        omega) h2) (fun o' m => cells o' (List.mem_cons_of_mem _ m))⟩

set_option maxHeartbeats 4000000 in
/-- The block-table constructor sequence from an aligned heap pointer above the block record: every table is
built at its record cell in constructor order between the entry and exit heap pointers, and every other word
below the entry heap pointer is kept. -/
theorem blockCtorSeq_run {F : Type} (B : BitVec 64) (tail : ProgHOL 64) :
    ∀ (specs : List (Nat × Nat × Nat)) (s : PanSemStateFiniteExact 64 F) (p oldT : BitVec 64), BlockPlan specs →
    s.code = originalRuntimeCode → s.globals.lookup (ofString "bs") = some (.val (.word B)) →
    s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) → p.toNat % 8 = 0 →
    (∀ a : BitVec 64, a.toNat < 33806089496 → s.memaddrs a) → B.toNat + 80 ≤ p.toNat →
    p.toNat + stateFreshTxAllocationBudget specs ≤ 33806089496 → blockClock specs ≤ s.clock →
    s.locals.lookup (ofString "t") = some (.val (.word oldT)) →
    ∃ (post : PanSemStateFiniteExact 64 F) (P : BitVec 64),
      evaluateHOLFiniteState s (blockCtorSeq specs tail) = evaluateHOLFiniteState post tail ∧
      BlockBuilt B specs post p.toNat P.toNat ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word P)) ∧ P.toNat % 8 = 0 ∧
      P.toNat ≤ 33806089496 ∧ p.toNat ≤ P.toNat ∧ P.toNat ≤ p.toNat + stateFreshTxAllocationBudget specs ∧
      (∀ a : BitVec 64, a.toNat < p.toNat → (∀ o ∈ specs.map (fun x => x.2.2), a ≠ B + BitVec.ofNat 64 o) →
        post.memory a = s.memory a) ∧
      post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ post.be = s.be ∧ HeapRel s.globals post.globals ∧
      (∃ v : BitVec 64, post.locals.lookup (ofString "t") = some (.val (.word v))) ∧
      s.clock ≤ post.clock + blockClock specs ∧ post.clock ≤ s.clock
  | [], s, p, oldT, _, _, _, heap, al, _, _, space, _, tL =>
    ⟨s,p,rfl,le_refl _,heap,al,by unfold stateFreshTxAllocationBudget at space; omega,le_refl _,
      by unfold stateFreshTxAllocationBudget; omega,fun _ _ _ => rfl,rfl,rfl,rfl,
      heapRel_preorder.refl _,⟨oldT,tL⟩,by unfold blockClock; omega,le_refl _⟩
  | (w,c,o) :: rest, s, p, oldT, ⟨wB,cB,⟨bits,power⟩,oB,fresh,plan⟩, code, hB, heap, al, domain, above, space, ticks, tL => by
    have cN : (BitVec.ofNat 64 c).toNat = c := Nat.mod_eq_of_lt cB
    change p.toNat + (81 * c + 114 + stateFreshTxAllocationBudget rest) ≤ _ at space
    change c + 14 + blockClock rest ≤ s.clock at ticks
    have oN : (B + BitVec.ofNat 64 o).toNat = B.toNat + o := off_toNat B o (by omega) (by omega)
    obtain ⟨r,keys,stride,used,values,order,orderPos,p',run,inv,kv,tables,cell,frame,rc,ra,rb,rrel,hp',le',al',in',pEq,tl,
      clk1,clk2⟩ := block_ctor_step s B p w c o bits (blockCtorSeq rest tail) code hB heap al domain wB cB power
        (by omega) (by omega) oldT tL (by omega)
    have bounds := stateFreshTx_next_table_bounds p w c wB cB (by omega)
    rw [← pEq] at bounds
    obtain ⟨post,P,run2,built,hP,alP,inP,leP,upP,frame2,pc,pa,pb,prel,ptl,pclk1,pclk2⟩ :=
      blockCtorSeq_run B tail rest r p' p plan (rc.trans code) (by rw [rrel.1 _ (by decide)]; exact hB) hp' al'
        (by rw [ra]; exact domain) (by omega) (by omega) (by omega) tl
    have offs := BlockPlan.offsets rest plan
    have restCells : ∀ a : BitVec 64, a.toNat < p'.toNat → p.toNat ≤ a.toNat → post.memory a = r.memory a :=
      fun a h1 h2 => frame2 a h1 (fun o' m e => by
        have := offs o' m
        rw [e] at h2; have := off_toNat B o' (by omega) (by omega); omega)
    obtain ⟨inv',tables'⟩ := inv.keep_block tables pa pb pc (fun a h1 h2 => restCells a (by omega) h1)
    refine ⟨post,P,?_,⟨p,keys,stride,used,values,order,orderPos,bits,p'.toNat,le_refl _,power,?_,inv',kv,tables',
      by omega,built⟩,hP,alP,inP,by omega,by change P.toNat ≤ p.toNat + (81 * c + 114 + stateFreshTxAllocationBudget rest); omega,
      ?_,pc.trans rc,pa.trans ra,pb.trans rb,
      heapRel_preorder.trans _ _ _ rrel prel,ptl,by unfold blockClock; omega,by omega⟩
    · unfold blockCtorSeq; rw [run]; exact run2
    · rw [frame2 _ (by omega) (fun o' m e => fresh (by
        have := offs o' m
        have := off_toNat B o' (by omega) (by omega)
        have : o = o' := by
          have := congrArg BitVec.toNat e; rw [oN] at this; omega
        rw [this]; exact m))]
      exact cell
    · intro a lt cells
      rw [frame2 a (by omega) (fun o' m => cells o' (List.mem_cons_of_mem _ m))]
      exact frame a lt (cells o (List.mem_cons_self ..))

#print axioms blockCtorSeq_run

/-- A constant-word store into a global record. -/
theorem block_store_const {F : Type} (s : PanSemStateFiniteExact 64 F) (B : BitVec 64) (o v : BitVec 64)
    (hB : s.globals.lookup (ofString "bs") = some (.val (.word B))) (dom : s.memaddrs (B + o)) (rest : ProgHOL 64) :
    evaluateHOLFiniteState s (.seq (.store (.op .add [.var .global (ofString "bs"),.const o]) (.const v)) rest) =
      evaluateHOLFiniteState (sourceWriteWord s (B + o) v) rest := by
  rw [evaluateHOLFiniteState_seq_line780,
    evaluate_store_word s (B + o) v _ _ (eval_add2 s _ _ _ _ (eval_global_word s _ B hB) (item_eval_const s _))
      (item_eval_const s _) dom]

theorem blockPlan_first : BlockPlan blockTablesFirst :=
  BlockPlan.cons 8 (by decide) (by decide) rfl (by decide) (by decide) <|
  BlockPlan.cons 8 (by decide) (by decide) rfl (by decide) (by decide) <|
  BlockPlan.cons 8 (by decide) (by decide) rfl (by decide) (by decide) <|
  BlockPlan.cons 6 (by decide) (by decide) rfl (by decide) (by decide) <|
  BlockPlan.cons 6 (by decide) (by decide) rfl (by decide) (by decide) <|
  BlockPlan.cons 6 (by decide) (by decide) rfl (by decide) (by decide) trivial

theorem blockPlan_last : BlockPlan blockTablesLast :=
  BlockPlan.cons 8 (by decide) (by decide) rfl (by decide) (by decide) trivial

set_option maxHeartbeats 4000000 in
/-- The block-state construction inside `state_init` (`bs = alloc(80)` through the last `htab_new`): the record
is the entry heap pointer, its `ws` cell and the two ancestor cells are set, and the seven block tables are built
at their record cells in constructor order above the record, all below the exit heap pointer. Words below the
entry heap pointer are kept; globals other than `bs` and `heap_ptr` are kept. -/
theorem block_segment_run {F : Type} (s : PanSemStateFiniteExact 64 F) (tail : ProgHOL 64) (p0 oldB W oldT : BitVec 64)
    (code : s.code = originalRuntimeCode)
    (hB : s.globals.lookup (ofString "bs") = some (.val (.word oldB)))
    (hW : s.globals.lookup (ofString "ws") = some (.val (.word W)))
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p0))) (al : p0.toNat % 8 = 0)
    (domain : ∀ a : BitVec 64, a.toNat < 33806089496 → s.memaddrs a)
    (space : p0.toNat + 88 + stateFreshTxAllocationBudget blockTablesFirst + stateFreshTxAllocationBudget blockTablesLast ≤
      33806089496)
    (ticks : 1 + blockClock blockTablesFirst + blockClock blockTablesLast ≤ s.clock)
    (tL : s.locals.lookup (ofString "t") = some (.val (.word oldT))) :
    ∃ (post : PanSemStateFiniteExact 64 F) (P1 P2 : BitVec 64),
      evaluateHOLFiniteState s (blockSegment tail) = evaluateHOLFiniteState post tail ∧
      post.globals.lookup (ofString "bs") = some (.val (.word p0)) ∧
      post.memory (p0 + 0) = .word W ∧ post.memory (p0 + 56) = .word 0 ∧ post.memory (p0 + 64) = .word 0 ∧
      BlockBuilt p0 blockTablesFirst post (allocationEnd p0 80).toNat P1.toNat ∧
      BlockBuilt p0 blockTablesLast post P1.toNat P2.toNat ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word P2)) ∧ P2.toNat % 8 = 0 ∧ P2.toNat ≤ 33806089496 ∧
      p0.toNat + 80 ≤ (allocationEnd p0 80).toNat ∧
      (∀ a : BitVec 64, a.toNat < p0.toNat → post.memory a = s.memory a) ∧
      (∀ name, name ≠ ofString "heap_ptr" → name ≠ ofString "bs" → post.globals.lookup name = s.globals.lookup name) ∧
      post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ post.be = s.be ∧
      s.clock ≤ post.clock + (1 + blockClock blockTablesFirst + blockClock blockTablesLast) ∧ post.clock ≤ s.clock := by
  have b1 : stateFreshTxAllocationBudget blockTablesFirst = 81 * 960 + 6 * 114 := by decide
  have b2 : stateFreshTxAllocationBudget blockTablesLast = 81 * 256 + 114 := by decide
  have c1 : blockClock blockTablesFirst = 960 + 6 * 14 := by decide
  have c2 : blockClock blockTablesLast = 256 + 14 := by decide
  rw [b1,b2] at space; rw [c1,c2] at ticks
  have cov := allocationEnd_covers p0 80 (by have : (80 : BitVec 64).toNat = 80 := rfl; rw [this]; omega)
  have e80 : (80 : BitVec 64).toNat = 80 := rfl
  rw [e80] at cov
  obtain ⟨a1,arun,aclk,amem,alocals,acode,aaddrs,abe,abs,aheap,aglob⟩ := evaluate_alloc_global_call s (.const 80) p0 80 oldB
    (ofString "bs") (by rw [evalListHOLFinite_eq_toExact]; rfl) code (by omega) heap hB (by decide)
    (by rw [BitVec.le_def,BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; have : (33806089496 : BitVec 64).toNat = 33806089496 := rfl; omega)]
        have : (33806089496 : BitVec 64).toNat = 33806089496 := rfl; omega)
    (by omega)
  have hk : ∀ k : Nat, k < 80 → (p0 + BitVec.ofNat 64 k).toNat = p0.toNat + k := fun k h => off_toNat p0 k (by omega) (by omega)
  have e0 : (p0 + 0).toNat = p0.toNat := hk 0 (by omega)
  have e56 : (p0 + 56).toNat = p0.toNat + 56 := hk 56 (by omega)
  have e64 : (p0 + 64).toNat = p0.toNat + 64 := hk 64 (by omega)
  have glob1 : ∀ name, name ≠ ofString "heap_ptr" → name ≠ ofString "bs" → a1.globals.lookup name = s.globals.lookup name :=
    fun name h1 h2 => aglob name h2 h1
  have hW1 : a1.globals.lookup (ofString "ws") = some (.val (.word W)) := by rw [glob1 _ (by decide) (by decide)]; exact hW
  have tL1 : a1.locals.lookup (ofString "t") = some (.val (.word oldT)) := by rw [alocals]; exact tL
  have dom1 : ∀ a : BitVec 64, a.toNat < 33806089496 → a1.memaddrs a := by rw [aaddrs]; exact domain
  have st0 := evaluate_store_word a1 (p0 + 0) W (.op .add [.var .global (ofString "bs"),.const 0]) (.var .global (ofString "ws"))
    (eval_add2 a1 _ _ _ _ (eval_global_word a1 _ p0 abs) (item_eval_const a1 _)) (eval_global_word a1 _ W hW1)
    (dom1 _ (by rw [e0]; omega))
  have p1N := cov
  obtain ⟨post1,P1,run1,built1,hP1,alP1,inP1,leP1,upP1,frame1,pc1,pa1,pb1,prel1,⟨t1,tl1⟩,clk11,clk12⟩ :=
    blockCtorSeq_run p0 (.seq (.store (.op .add [.var .global (ofString "bs"),.const 56]) (.const 0))
        (.seq (.store (.op .add [.var .global (ofString "bs"),.const 64]) (.const 0)) (blockCtorSeq blockTablesLast tail)))
      blockTablesFirst (sourceWriteWord a1 (p0 + 0) W) (allocationEnd p0 80) oldT blockPlan_first (acode.trans code) abs aheap cov.2.2 dom1 (by omega)
      (by rw [b1]; omega) (by change _ ≤ a1.clock; rw [c1,aclk]; omega) tL1
  rw [b1] at upP1
  have q1 := cov.1
  have offs1 : blockTablesFirst.map (fun x => x.2.2) = [8,16,24,32,40,48] := rfl
  have bs1 : post1.globals.lookup (ofString "bs") = some (.val (.word p0)) := by rw [prel1.1 _ (by decide)]; exact abs
  have sclk : (sourceWriteWord a1 (p0 + 0) W).clock = a1.clock := rfl
  rw [sclk,aclk] at clk11
  have dom2 : ∀ a : BitVec 64, a.toNat < 33806089496 → post1.memaddrs a := by rw [pa1]; exact dom1
  let s3 := sourceWriteWord post1 (p0 + 56) 0
  let s4 := sourceWriteWord s3 (p0 + 64) 0
  have bs4 : s4.globals.lookup (ofString "bs") = some (.val (.word p0)) := bs1
  obtain ⟨post,P2,run2,built2,hP2,alP2,inP2,leP2,upP2,frame2,pc2,pa2,pb2,prel2,_,clk21,clk22⟩ :=
    blockCtorSeq_run p0 tail blockTablesLast s4 P1 t1 blockPlan_last (pc1.trans (acode.trans code)) bs4 hP1 alP1
      (by exact dom2) (by omega) (by rw [b2]; omega) (by change _ ≤ post1.clock; rw [c2]; omega) tl1
  have n72 : (p0 + BitVec.ofNat 64 72).toNat = p0.toNat + 72 := hk 72 (by omega)
  have m4 : ∀ a : BitVec 64, a ≠ p0 + 56 → a ≠ p0 + 64 → s4.memory a = post1.memory a := by
    intro a h1 h2; simp only [s4,s3,sourceWriteWord,if_neg h1,if_neg h2]
  have keepLast : ∀ a : BitVec 64, a.toNat < P1.toNat → a ≠ p0 + BitVec.ofNat 64 72 → post.memory a = s4.memory a :=
    fun a lt ne => frame2 a lt (fun o m => by
      have l : blockTablesLast.map (fun x => x.2.2) = [72] := rfl
      rw [l,List.mem_singleton] at m
      rw [m]; exact ne)
  have postTo1 : ∀ a : BitVec 64, a.toNat < P1.toNat → a ≠ p0 + BitVec.ofNat 64 72 → a ≠ p0 + 56 → a ≠ p0 + 64 →
      post.memory a = post1.memory a := fun a lt n1 n2 n3 => by rw [keepLast a lt n1,m4 a n2 n3]
  have b1le := BlockBuilt.le _ _ _ _ built1
  have hne : ∀ a b : BitVec 64, a.toNat ≠ b.toNat → a ≠ b := fun a b h e => h (by rw [e])
  refine ⟨post,P1,P2,?_,?_,?_,?_,?_,?_,built2,hP2,alP2,inP2,cov.1,?_,?_,pc2.trans (pc1.trans acode),
    pa2.trans (pa1.trans aaddrs),pb2.trans (pb1.trans abe),?_,by
      have h4 : s4.clock = post1.clock := rfl
      rw [sclk] at clk12; omega⟩
  · unfold blockSegment
    rw [evaluateHOLFiniteState_seq_line780,arun]; dsimp only
    rw [evaluateHOLFiniteState_seq_line780,st0]; dsimp only
    rw [run1,block_store_const post1 p0 56 0 bs1 (dom2 _ (by rw [e56]; omega)),
      block_store_const s3 p0 64 0 bs1 (by show post1.memaddrs _; exact dom2 _ (by rw [e64]; omega))]
    exact run2
  · rw [prel2.1 _ (by decide)]; exact bs4
  · rw [postTo1 _ (by omega) (hne _ _ (by rw [n72]; omega)) (hne _ _ (by rw [e56]; omega))
      (hne _ _ (by rw [e64]; omega)),
      frame1 _ (by omega) (fun o m => by rw [offs1] at m; exact hne _ _ (by
        have := hk o (by simp at m; omega); simp at m; omega))]
    simp [sourceWriteWord]
  · rw [keepLast _ (by have := e56; omega) (hne _ _ (by rw [n72,e56]; omega))]
    simp [s4,s3,sourceWriteWord]
  · rw [keepLast _ (by have := e64; omega) (hne _ _ (by rw [n72,e64]; omega))]
    simp [s4,s3,sourceWriteWord]
  · refine BlockBuilt.keep _ _ _ _ _ built1 (pa2.trans rfl) (pb2.trans rfl) (pc2.trans rfl) (fun a h1 h2 => ?_)
      (fun o m => ?_)
    · rw [postTo1 a h2 (hne _ _ (by rw [n72]; omega)) (hne _ _ (by rw [e56]; omega)) (hne _ _ (by rw [e64]; omega))]
    · rw [offs1] at m
      have ob : o ≤ 48 := by simp at m; omega
      have := hk o (by omega)
      rw [postTo1 _ (by omega) (hne _ _ (by rw [n72]; omega)) (hne _ _ (by rw [e56]; simp at m; omega))
        (hne _ _ (by rw [e64]; simp at m; omega))]
  · intro a lt
    rw [postTo1 a (by omega) (hne _ _ (by rw [n72]; omega)) (hne _ _ (by rw [e56]; omega))
      (hne _ _ (by rw [e64]; omega)),
      frame1 a (by omega) (fun o m => by rw [offs1] at m; exact hne _ _ (by have := hk o (by simp at m; omega); omega))]
    simp only [sourceWriteWord,if_neg (hne _ _ (by rw [e0]; omega) : a ≠ p0 + 0)]
    rw [amem]
  · intro name h1 h2
    rw [prel2.1 _ h1]; change post1.globals.lookup name = _; rw [prel1.1 _ h1]; exact glob1 name h1 h2
  · rw [c1,c2]
    change post1.clock ≤ a1.clock at clk12
    rw [c1] at clk11; rw [c2] at clk21
    have : s4.clock = post1.clock := rfl
    change post1.clock ≤ post.clock + _ at clk21
    omega

#print axioms block_segment_run

/-- Any built block table, by its constructor entry. -/
theorem BlockBuilt.entry {F : Type} {B : BitVec 64} :
    ∀ (specs : List (Nat × Nat × Nat)) (s : PanSemStateFiniteExact 64 F) (lo hi : Nat), BlockBuilt B specs s lo hi →
    ∀ w c o, (w,c,o) ∈ specs →
    ∃ (t keys stride used values order orderPos : BitVec 64) (bits : Nat),
      s.memory (B + BitVec.ofNat 64 o) = .word t ∧
      HtabAligned (BitVec.ofNat 64 w) t keys stride (BitVec.ofNat 64 c) used values order orderPos 0 bits s ∧
      keys.toNat + (BitVec.ofNat 64 c).toNat * stride.toNat ≤ values.toNat ∧
      OrderInv s (BitVec.ofNat 64 c) 0 used order orderPos ∧ (BitVec.ofNat 64 c).toNat = 2 ^ bits ∧
      lo ≤ t.toNat ∧ orderPos.toNat + (BitVec.ofNat 64 c).toNat * 8 ≤ hi
  | [], _, _, _, _, _, _, _, m => by simp at m
  | (w',c',o') :: rest, s, lo, hi, ⟨t,keys,stride,used,values,order,orderPos,bits,mid,l1,_,cell,inv,kv,tables,l2,h⟩,
      w, c, o, m => by
    have midHi := BlockBuilt.le rest s mid hi h
    rcases List.mem_cons.mp m with e | m
    · simp only [Prod.mk.injEq] at e
      obtain ⟨rfl,rfl,rfl⟩ := e
      exact ⟨t,keys,stride,used,values,order,orderPos,bits,cell,inv,kv,tables,inv.power,l1,by omega⟩
    · obtain ⟨t',k',st',u',v',or',op',b',c1,i1,kv1,t1,p1,l1',h1⟩ := BlockBuilt.entry rest s mid hi h w c o m
      have := inv.headerKeys; have := inv.keysBefore; have := inv.usedBefore; have := inv.orderBefore
      exact ⟨t',k',st',u',v',or',op',b',c1,i1,kv1,t1,p1,by omega,h1⟩

#print axioms BlockBuilt.entry

/-- A freshly built table as a union destination (the destination half of `UnionPair.Ready`): laid out as an
aligned table, the order invariant, room, and the aligned-cell domain from the full heap domain. -/
theorem block_dst_ready {F : Type} {s : PanSemStateFiniteExact 64 F}
    {keyLength t keys stride capacity used values order orderPos : BitVec 64} {bits : Nat}
    (inv : HtabAligned keyLength t keys stride capacity used values order orderPos 0 bits s)
    (tables : OrderInv s capacity 0 used order orderPos)
    (domain : ∀ a : BitVec 64, a.toNat < 33806089496 → s.memaddrs a) :
    HtabLaid keyLength t keys stride capacity used values order orderPos 0 bits (min keys.toNat values.toNat)
      (orderPos.toNat + capacity.toNat * 8) s ∧ OrderInv s capacity 0 used order orderPos ∧
      (0 : BitVec 64).toNat < capacity.toNat ∧
      (∀ a : BitVec 64, a.toNat % 8 = 0 → t.toNat ≤ a.toNat → a.toNat < 33806089496 → s.memaddrs a) := by
  have p := inv.power
  have : 0 < 2 ^ bits := Nat.two_pow_pos bits
  exact ⟨Or.inl ⟨inv,rfl,rfl⟩,tables,by rw [p]; exact this,fun a _ _ h => domain a h⟩

/-- A freshly built table as the block storage map with the empty inner registry: values tracked (vacuously). -/
theorem block_bouter_empty {F : Type} {s : PanSemStateFiniteExact 64 F}
    {keyLength t keys stride capacity used values order orderPos : BitVec 64} {bits : Nat}
    (inv : HtabAligned keyLength t keys stride capacity used values order orderPos 0 bits s)
    (kv : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat) :
    VTabs ∅ s capacity 0 used keys stride values order :=
  ⟨fun k h => absurd h (by simp),
   fun q inside occupied => absurd ((hashOccupiedCount_zero_reads capacity (hashOccupancyRead s used)
     (by rw [← inv.agreement]; rfl)) q inside) occupied,
   Or.inl kv⟩

#print axioms block_dst_ready
#print axioms block_bouter_empty
end InitECandidate.Runtime
