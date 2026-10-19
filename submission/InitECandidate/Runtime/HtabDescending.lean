import InitECandidate.Runtime.HtabRegions
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem runBounded_growTail_regions {F : Type} (s r : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count ncap p0 p1 p2 p3 p4 p5 : BitVec 64) (bits : Nat)
    (inv : HtabRegions keyLength table keys stride capacity used values order orderPos count bits s)
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
    (budget : ncap.toNat + 1 + (0 + (0 + (0 + (0 + (0 + (0 + (0 +
      (count.toNat * (insertCallCost keyLength ncap + 1) + 0)))))))) ≤ r.clock) :
    RunBounded r (.seq (.call (some (none,none)) (ofString "memzero") [.var .local (ofString "nused"),.var .local (ofString "ncap")])
      (htabGrowHeaderStores (.dec (ofString "k") .one (.const 0) (.seq hashGrowRehashLoop (.return (.const 0))))))
      (ncap.toNat + 1 + (0 + (0 + (0 + (0 + (0 + (0 + (0 +
        (count.toNat * (insertCallCost keyLength ncap + 1) + 0))))))))) := by
  -- arithmetic on the old and fresh layouts
  have capSmall : capacity.toNat ≤ 33806089496 := by have := inv.usedEnd; omega
  have ncapNat : ncap.toNat = capacity.toNat * 2 := by
    rw [ncapEq]; exact BitVec.toNat_mul_of_lt (by change capacity.toNat * 2 < 2 ^ 64; omega)
  have strideProd : capacity.toNat * stride.toNat ≤ 33806089496 := by
    have := inv.keysEnd; omega
  have keysSize : (ncap * stride).toNat = ncap.toNat * stride.toNat := by
    apply BitVec.toNat_mul_of_lt
    rw [ncapNat]
    have : capacity.toNat * 2 * stride.toNat = 2 * (capacity.toNat * stride.toNat) := by
      rw [Nat.mul_comm capacity.toNat 2,Nat.mul_assoc]
    rw [this]
    change _ < 2 ^ 64
    omega
  have eightSize : (ncap * 8).toNat = ncap.toNat * 8 :=
    BitVec.toNat_mul_of_lt (by rw [ncapNat]; change capacity.toNat * 2 * 8 < 2 ^ 64; omega)
  obtain ⟨l0,a1,_⟩ := alloc_step_layout p0 (ncap * stride) p0Inside A.r0
  obtain ⟨l1,a2,_⟩ := alloc_step_layout p1 (ncap * 8) A.f1 A.r1
  obtain ⟨l2,a3,_⟩ := alloc_step_layout p2 ncap A.f2 A.r2
  obtain ⟨l3,a4,_⟩ := alloc_step_layout p3 (ncap * 8) A.f3 A.r3
  obtain ⟨l4,a5,_⟩ := alloc_step_layout p4 (ncap * 8) A.f4 A.r4
  rw [← A.e1] at l0 a1
  rw [← A.e2] at l1 a2
  rw [← A.e3] at l2 a3
  rw [← A.e4] at l3 a4
  rw [← A.e5] at l4 a5
  rw [keysSize] at l0
  rw [eightSize] at l1 l3 l4
  have f5 := A.f5
  -- the memzero call through the aligned-cells contract
  have rUsed : r.locals.lookup (ofString "nused") = some (.val (.word p2)) := A.nused
  have rNcap : r.locals.lookup (ofString "ncap") = some (.val (.word ncap)) := (A.others _ (by decide)).trans ncapL
  have zeroArgs : evalListHOLFinite r (h := fun a => Classical.propDecidable (r.memaddrs a))
      [.var .local (ofString "nused"),.var .local (ofString "ncap")] = some [.val (.word p2),.val (.word ncap)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,rUsed,rNcap]
  have rCode : r.code = originalRuntimeCode := A.code.trans inv.code
  obtain ⟨m,zeroRun,_,zc1,zc2,_,zcode,zaddr,zbe,zlocals,zocc⟩ := evaluate_memzero_aligned_call_cells r _ _ p2 ncap zeroArgs rCode
    (by omega) (by omega) a2
    (by
      intro offset inside
      rw [A.memaddrs]
      have align := byteAlign_toNat (p2 + BitVec.ofNat 64 offset)
      have sum : (p2 + BitVec.ofNat 64 offset).toNat = p2.toNat + offset := word_add_toNat p2 offset (by omega)
      rw [sum] at align
      exact arena _ (by rw [align]; omega) (by rw [align]; omega) (by rw [align]; omega))
  have zeroFrame : ∀ watched : BitVec 64, (watched.toNat < p2.toNat ∨ p2.toNat + ncap.toNat ≤ watched.toNat) →
      m.memory watched = s.memory watched := by
    intro watched outside
    rw [(memzero_call_normal_memory r m _ p2 ncap watched zeroArgs rCode a2 (by omega) outside zeroRun).1,A.memory]
  refine RunBounded.seq (by unfold RunBounded; rw [zeroRun]; exact ⟨by dsimp only; omega,zc2,by simp⟩) (by omega) ?_
  intro next run _ _
  rw [zeroRun] at run
  obtain ⟨_,rfl⟩ := Prod.mk.inj run
  -- locals after memzero
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
  unfold htabGrowHeaderStores
  apply runBounded_store_step m _ _ (table + 16) ncap (eval_hashLocalAddress m _ table 16 mT)
    (by simp [evalHOLExact,mNcap]) mCode (by omega)
  intro w1 l1 c1 k1 a1' b1 g1 mem1
  apply runBounded_store_step w1 _ _ (table + 32) p0 (eval_hashLocalAddress w1 _ table 32 (by rw [l1]; exact mT))
    (by simp [evalHOLExact,l1,mKeys]) (c1.trans mCode) (by rw [k1]; omega)
  intro w2 l2 c2 k2 a2' b2 g2 mem2
  apply runBounded_store_step w2 _ _ (table + 40) p1 (eval_hashLocalAddress w2 _ table 40 (by rw [l2,l1]; exact mT))
    (by simp [evalHOLExact,l2,l1,mVals]) (c2.trans (c1.trans mCode)) (by rw [k2,k1]; omega)
  intro w3 l3 c3 k3 a3' b3 g3 mem3
  apply runBounded_store_step w3 _ _ (table + 48) p2 (eval_hashLocalAddress w3 _ table 48 (by rw [l3,l2,l1]; exact mT))
    (by simp [evalHOLExact,l3,l2,l1,mUsed]) (c3.trans (c2.trans (c1.trans mCode))) (by rw [k3,k2,k1]; omega)
  intro w4 l4 c4 k4 a4' b4 g4 mem4
  apply runBounded_store_step w4 _ _ (table + 56) p3 (eval_hashLocalAddress w4 _ table 56 (by rw [l4,l3,l2,l1]; exact mT))
    (by simp [evalHOLExact,l4,l3,l2,l1,mOrder]) (c4.trans (c3.trans (c2.trans (c1.trans mCode)))) (by rw [k4,k3,k2,k1]; omega)
  intro w5 l5 c5 k5 a5' b5 g5 mem5
  apply runBounded_store_step w5 _ _ (table + 64) p4
    (eval_hashLocalAddress w5 _ table 64 (by rw [l5,l4,l3,l2,l1]; exact mT))
    (by simp [evalHOLExact,l5,l4,l3,l2,l1,mOrderPos]) (c5.trans (c4.trans (c3.trans (c2.trans (c1.trans mCode)))))
    (by rw [k5,k4,k3,k2,k1]; omega)
  intro w6 l6 c6 k6 a6' b6 g6 mem6
  apply runBounded_store_step w6 _ _ (table + 24) 0
    (eval_hashLocalAddress w6 _ table 24 (by rw [l6,l5,l4,l3,l2,l1]; exact mT))
    (by simp [evalHOLExact]) (c6.trans (c5.trans (c4.trans (c3.trans (c2.trans (c1.trans mCode))))))
    (by rw [k6,k5,k4,k3,k2,k1]; omega)
  intro w7 l7 c7 k7 a7' b7 g7 mem7
  have tFits : table.toNat + 72 < 2 ^ 64 := by omega
  have hdr : ∀ k : Nat, k ≤ 64 → (table + BitVec.ofNat 64 k).toNat = table.toNat + k :=
    fun k hk => word_add_toNat table k (by omega)
  -- memory of the fresh header and arrays
  have untouched : ∀ x : BitVec 64, x ≠ table + 16 → x ≠ table + 32 → x ≠ table + 40 → x ≠ table + 48 →
      x ≠ table + 56 → x ≠ table + 64 → x ≠ table + 24 → w7.memory x = m.memory x := by
    intro x n16 n32 n40 n48 n56 n64 n24
    rw [mem7,if_neg n24,mem6,if_neg n64,mem5,if_neg n56,mem4,if_neg n48,mem3,if_neg n40,mem2,if_neg n32,mem1,if_neg n16]
  have ne : ∀ i j : Nat, i ≤ 64 → j ≤ 64 → i ≠ j → table + BitVec.ofNat 64 i ≠ table + BitVec.ofNat 64 j :=
    fun i j hi hj h => header_ne table tFits i j hi hj h
  have c16 : w7.memory (table + 16) = .word ncap := by
    rw [mem7,if_neg (by exact ne 16 24 (by omega) (by omega) (by omega)),mem6,if_neg (by exact ne 16 64 (by omega) (by omega) (by omega)),
      mem5,if_neg (by exact ne 16 56 (by omega) (by omega) (by omega)),mem4,if_neg (by exact ne 16 48 (by omega) (by omega) (by omega)),
      mem3,if_neg (by exact ne 16 40 (by omega) (by omega) (by omega)),mem2,if_neg (by exact ne 16 32 (by omega) (by omega) (by omega)),
      mem1,if_pos rfl]
  have c32 : w7.memory (table + 32) = .word p0 := by
    rw [mem7,if_neg (by exact ne 32 24 (by omega) (by omega) (by omega)),mem6,if_neg (by exact ne 32 64 (by omega) (by omega) (by omega)),
      mem5,if_neg (by exact ne 32 56 (by omega) (by omega) (by omega)),mem4,if_neg (by exact ne 32 48 (by omega) (by omega) (by omega)),
      mem3,if_neg (by exact ne 32 40 (by omega) (by omega) (by omega)),mem2,if_pos rfl]
  have c40 : w7.memory (table + 40) = .word p1 := by
    rw [mem7,if_neg (by exact ne 40 24 (by omega) (by omega) (by omega)),mem6,if_neg (by exact ne 40 64 (by omega) (by omega) (by omega)),
      mem5,if_neg (by exact ne 40 56 (by omega) (by omega) (by omega)),mem4,if_neg (by exact ne 40 48 (by omega) (by omega) (by omega)),
      mem3,if_pos rfl]
  have c48 : w7.memory (table + 48) = .word p2 := by
    rw [mem7,if_neg (by exact ne 48 24 (by omega) (by omega) (by omega)),mem6,if_neg (by exact ne 48 64 (by omega) (by omega) (by omega)),
      mem5,if_neg (by exact ne 48 56 (by omega) (by omega) (by omega)),mem4,if_pos rfl]
  have c56 : w7.memory (table + 56) = .word p3 := by
    rw [mem7,if_neg (by exact ne 56 24 (by omega) (by omega) (by omega)),mem6,if_neg (by exact ne 56 64 (by omega) (by omega) (by omega)),
      mem5,if_pos rfl]
  have c64 : w7.memory (table + 64) = .word p4 := by
    rw [mem7,if_neg (by exact ne 64 24 (by omega) (by omega) (by omega)),mem6,if_pos rfl]
  have c24 : w7.memory (table + 24) = .word 0 := by rw [mem7,if_pos rfl]
  have oldCell : ∀ k : Nat, k ≤ 64 → k ≠ 16 → k ≠ 32 → k ≠ 40 → k ≠ 48 → k ≠ 56 → k ≠ 64 → k ≠ 24 →
      w7.memory (table + BitVec.ofNat 64 k) = s.memory (table + BitVec.ofNat 64 k) := by
    intro k hk e16 e32 e40 e48 e56 e64 e24
    rw [untouched _ (by exact ne k 16 hk (by omega) e16) (by exact ne k 32 hk (by omega) e32)
      (by exact ne k 40 hk (by omega) e40) (by exact ne k 48 hk (by omega) e48) (by exact ne k 56 hk (by omega) e56)
      (by exact ne k 64 hk (by omega) e64) (by exact ne k 24 hk (by omega) e24)]
    apply zeroFrame
    left; rw [hdr k hk]; omega
  have c0 : w7.memory (table + 0) = .word keyLength :=
    (oldCell 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans inv.cell0
  have c8 : w7.memory (table + 8) = .word stride :=
    (oldCell 8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans inv.cell8
  have wAddr : w7.memaddrs = s.memaddrs := a7'.trans (a6'.trans (a5'.trans (a4'.trans (a3'.trans (a2'.trans (a1'.trans
    (zaddr.trans A.memaddrs)))))))
  have wBe : w7.be = s.be := b7.trans (b6.trans (b5.trans (b4.trans (b3.trans (b2.trans (b1.trans (zbe.trans A.be)))))))
  have wCode : w7.code = originalRuntimeCode := c7.trans (c6.trans (c5.trans (c4.trans (c3.trans (c2.trans (c1.trans mCode))))))
  have wClock : w7.clock = m.clock := k7.trans (k6.trans (k5.trans (k4.trans (k3.trans (k2.trans k1)))))
  have wLocals : w7.locals = m.locals := l7.trans (l6.trans (l5.trans (l4.trans (l3.trans (l2.trans l1)))))
  have byteFar : ∀ slot : BitVec 64, slot.toNat < ncap.toNat → ∀ k : Nat, k ≤ 64 →
      panByteAlignHOL (p2 + slot) ≠ table + BitVec.ofNat 64 k := by
    intro slot inside k hk
    apply word_ne_of_toNat
    rw [byteAlign_toNat,BitVec.toNat_add_of_lt (by omega),hdr k hk]
    omega
  have readSame : ∀ slot : BitVec 64, slot.toNat < ncap.toNat → hashOccupancyRead w7 p2 slot = hashOccupancyRead m p2 slot := by
    intro slot inside
    apply occupancyRead_congr_at w7 m p2 slot ?_ (wAddr.trans (zaddr.trans A.memaddrs).symm)
      (wBe.trans (zbe.trans A.be).symm)
    exact untouched _ (by exact byteFar slot inside 16 (by omega)) (by exact byteFar slot inside 32 (by omega))
      (by exact byteFar slot inside 40 (by omega)) (by exact byteFar slot inside 48 (by omega))
      (by exact byteFar slot inside 56 (by omega)) (by exact byteFar slot inside 64 (by omega))
      (by exact byteFar slot inside 24 (by omega))
  have zeroCount : hashOccupiedCount ncap (hashOccupancyRead w7 p2) = 0 := by
    rw [hashOccupiedCount_congr ncap _ _ readSame]; exact zocc
  apply RunBounded.decConst
  generalize he : setVarHOLFinite (ofString "k") (.val (.word (0 : BitVec 64))) w7 = e
  have eLocal : ∀ k, k ∉ growAllocNames → k ≠ ofString "k" → e.locals.lookup k = s.locals.lookup k := by
    intro k notIn nk
    rw [← he]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm nk]
    rw [wLocals]
    exact mLocal k notIn
  have eInv : HtabAligned keyLength table p0 stride ncap p2 p1 p3 p4 0 (bits + 1) e := by
    have em : e.memory = w7.memory := by rw [← he]; rfl
    have ea : e.memaddrs = s.memaddrs := by rw [← he]; exact wAddr
    exact {
      code := by rw [← he]; exact wCode
      power := by rw [ncapNat,inv.power,Nat.pow_succ]
      tableAligned := inv.tableAligned
      keysAligned := p0Aligned
      strideAligned := inv.strideAligned
      valuesAligned := a1
      usedAligned := a2
      orderAligned := a3
      orderPosAligned := a4
      headerKeys := headerBelow
      headerValues := by omega
      keysBefore := by omega
      valuesBefore := by omega
      usedBefore := by omega
      orderBefore := by omega
      endBound := by omega
      fits := inv.fits
      domain := fun a h1 h2 h3 => by rw [ea]; exact arena a h1 h2 (by omega)
      cell0 := by rw [em]; exact c0
      cell8 := by rw [em]; exact c8
      cell16 := by rw [em]; exact c16
      cell24 := by rw [em]; exact c24
      cell32 := by rw [em]; exact c32
      cell40 := by rw [em]; exact c40
      cell48 := by rw [em]; exact c48
      cell56 := by rw [em]; exact c56
      cell64 := by rw [em]; exact c64
      agreement := by
        have : hashOccupancyRead e p2 = hashOccupancyRead w7 p2 := by
          funext slot; unfold hashOccupancyRead; rw [← he]; rfl
        rw [this,zeroCount]; rfl }
  have eCode : e.code = originalRuntimeCode := eInv.code
  have eClock : e.clock = m.clock := by rw [← he]; exact wClock
  have ranked : GrowRehashRank keyLength table p0 stride ncap p2 p1 p3 p4 count (bits + 1) e count.toNat :=
    ⟨0,by rw [← he]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],by simp,by simp,
      (eLocal _ (by decide) (by decide)).trans itemsL,(eLocal _ (by decide) (by decide)).trans tL,
      ⟨keys,(eLocal _ (by decide) (by decide)).trans keysL⟩,⟨stride,(eLocal _ (by decide) (by decide)).trans strideL⟩,
      ⟨values,(eLocal _ (by decide) (by decide)).trans valsL⟩,⟨order,(eLocal _ (by decide) (by decide)).trans orderL⟩,
      eInv⟩
  have loop := growRehashLoop_run keyLength table p0 stride ncap p2 p1 p3 p4 count (bits + 1) (by omega)
    (by omega) small count.toNat e eCode ranked (by rw [eClock]; omega)
  refine RunBounded.seq ⟨loop.1,loop.2.1,loop.2.2.1⟩ (by rw [eClock]; omega) ?_
  intro final _ finalCode _
  exact RunBounded.ofProg (ProgBounded.straight _ (by decide)) (finalCode.trans eCode) (Nat.zero_le _)

#print axioms runBounded_growTail_regions

theorem evaluate_htabGrow_body_bounded_regions {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count pointer : BitVec 64) (bits : Nat)
    (inv : HtabRegions keyLength table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerAligned : pointer.toNat % 8 = 0) (headerBelow : table.toNat + 72 ≤ pointer.toNat)
    (pointerInside : pointer.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → table.toNat ≤ a.toNat → a.toNat < 33806089496 → state.memaddrs a)
    (room : count.toNat < capacity.toNat) (small : keyLength.toNat ≤ 33806089496)
    (budget : growBodyCost keyLength capacity count ≤ state.clock) :
    RunBounded state (sourceFunctionBody Guest.guestFn_htab_grow) (growBodyCost keyLength capacity count) := by
  unfold growBodyCost at budget ⊢
  rw [source_htabGrow_body]
  apply runBounded_header_load _ _ _ table 16 capacity _ tableLocal (inv.header_domain 16 (by omega) (by omega)) inv.cell16
  apply runBounded_header_load _ _ _ table 8 stride _
    (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
    (by exact inv.header_domain 8 (by omega) (by omega)) (by exact inv.cell8)
  apply runBounded_header_load _ _ _ table 32 keys _
    (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
    (by exact inv.header_domain 32 (by omega) (by omega)) (by exact inv.cell32)
  apply runBounded_header_load _ _ _ table 40 values _
    (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
    (by exact inv.header_domain 40 (by omega) (by omega)) (by exact inv.cell40)
  apply runBounded_header_load _ _ _ table 56 order _
    (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
    (by exact inv.header_domain 56 (by omega) (by omega)) (by exact inv.cell56)
  apply runBounded_header_load _ _ _ table 24 count _
    (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
    (by exact inv.header_domain 24 (by omega) (by omega)) (by exact inv.cell24)
  generalize hs6 : setVarHOLFinite (ofString "nitems") (.val (.word count)) (setVarHOLFinite (ofString "order") (.val (.word order))
    (setVarHOLFinite (ofString "vals") (.val (.word values)) (setVarHOLFinite (ofString "keys") (.val (.word keys))
      (setVarHOLFinite (ofString "stride") (.val (.word stride))
        (setVarHOLFinite (ofString "cap") (.val (.word capacity)) state))))) = s6
  have s6Facts : s6.memory = state.memory ∧ s6.memaddrs = state.memaddrs ∧ s6.be = state.be ∧ s6.code = state.code ∧
      s6.clock = state.clock ∧ s6.globals = state.globals := by
    rw [← hs6]; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  have s6cap : s6.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    rw [← hs6]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  apply RunBounded.decWord s6 _ _ (capacity * 2) (eval_htabGrow_doubled_capacity s6 capacity s6cap)
  generalize hs7 : setVarHOLFinite (ofString "ncap") (.val (.word (capacity * 2))) s6 = s7
  have s7Facts : s7.memory = state.memory ∧ s7.memaddrs = state.memaddrs ∧ s7.be = state.be ∧ s7.code = state.code ∧
      s7.clock = state.clock ∧ s7.globals = state.globals := by
    rw [← hs7]; exact s6Facts
  have lk : ∀ name : MlS, s7.locals.lookup name = (setVarHOLFinite (ofString "ncap") (.val (.word (capacity * 2)))
      (setVarHOLFinite (ofString "nitems") (.val (.word count)) (setVarHOLFinite (ofString "order") (.val (.word order))
        (setVarHOLFinite (ofString "vals") (.val (.word values)) (setVarHOLFinite (ofString "keys") (.val (.word keys))
          (setVarHOLFinite (ofString "stride") (.val (.word stride))
            (setVarHOLFinite (ofString "cap") (.val (.word capacity)) state))))))).locals.lookup name := by
    intro name; rw [← hs7,← hs6]
  have inv7 := inv.transfer s7Facts.1 s7Facts.2.1 s7Facts.2.2.1 s7Facts.2.2.2.1
  apply runBounded_growAllocs s7 _ (capacity * 2) stride pointer
    (by rw [lk]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by rw [lk]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (s7Facts.2.2.2.1.trans inv.code) (by rw [s7Facts.2.2.2.2.2]; exact heap) (by rw [s7Facts.2.2.2.2.1]; exact budget)
  intro r p1 p2 p3 p4 p5 A tc
  exact runBounded_growTail_regions s7 r keyLength table keys stride capacity used values order orderPos count (capacity * 2)
    pointer p1 p2 p3 p4 p5 bits inv7
    (by rw [lk]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
    (by rw [lk]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by rw [lk]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by rw [lk]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by rw [lk]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by rw [lk]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by rw [lk]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    rfl A pointerAligned headerBelow pointerInside
    (fun a h1 h2 h3 => by rw [s7Facts.2.1]; exact arena a h1 h2 h3) room small tc

#print axioms evaluate_htabGrow_body_bounded_regions

theorem grow_fresh_aligned_regions {F : Type} (s r m w7 : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count ncap p0 p1 p2 p3 p4 p5 : BitVec 64) (bits : Nat)
    (inv : HtabRegions keyLength table keys stride capacity used values order orderPos count bits s)
    (ncapEq : ncap = capacity * 2) (A : GrowAllocated s r ncap stride p0 p1 p2 p3 p4 p5)
    (p0Aligned : p0.toNat % 8 = 0) (headerBelow : table.toNat + 72 ≤ p0.toNat) (p0Inside : p0.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → table.toNat ≤ a.toNat → a.toNat < 33806089496 → s.memaddrs a)
    (zeroFrame : ∀ watched : BitVec 64, (watched.toNat < p2.toNat ∨ p2.toNat + ncap.toNat ≤ watched.toNat) →
      m.memory watched = s.memory watched)
    (zocc : hashOccupiedCount ncap (hashOccupancyRead m p2) = 0)
    (mAddr : m.memaddrs = s.memaddrs) (mBe : m.be = s.be)
    (wMemory : ∀ x : BitVec 64, w7.memory x =
      if x = table + 24 then .word 0 else if x = table + 64 then .word p4 else if x = table + 56 then .word p3 else
      if x = table + 48 then .word p2 else if x = table + 40 then .word p1 else if x = table + 32 then .word p0 else
      if x = table + 16 then .word ncap else m.memory x)
    (wAddr : w7.memaddrs = m.memaddrs) (wBe : w7.be = m.be) (wCode : w7.code = originalRuntimeCode) :
    HtabAligned keyLength table p0 stride ncap p2 p1 p3 p4 0 (bits + 1) w7 := by
  have capSmall : capacity.toNat ≤ 33806089496 := by have := inv.usedEnd; omega
  have ncapNat : ncap.toNat = capacity.toNat * 2 := by
    rw [ncapEq]; exact BitVec.toNat_mul_of_lt (by change capacity.toNat * 2 < 2 ^ 64; omega)
  have strideProd : capacity.toNat * stride.toNat ≤ 33806089496 := by
    have := inv.keysEnd; omega
  have keysSize : (ncap * stride).toNat = ncap.toNat * stride.toNat := by
    apply BitVec.toNat_mul_of_lt
    rw [ncapNat]
    have : capacity.toNat * 2 * stride.toNat = 2 * (capacity.toNat * stride.toNat) := by
      rw [Nat.mul_comm capacity.toNat 2,Nat.mul_assoc]
    rw [this]
    change _ < 2 ^ 64
    omega
  have eightSize : (ncap * 8).toNat = ncap.toNat * 8 :=
    BitVec.toNat_mul_of_lt (by rw [ncapNat]; change capacity.toNat * 2 * 8 < 2 ^ 64; omega)
  obtain ⟨l0,a1,_⟩ := alloc_step_layout p0 (ncap * stride) p0Inside A.r0
  obtain ⟨l1,a2,_⟩ := alloc_step_layout p1 (ncap * 8) A.f1 A.r1
  obtain ⟨l2,a3,_⟩ := alloc_step_layout p2 ncap A.f2 A.r2
  obtain ⟨l3,a4,_⟩ := alloc_step_layout p3 (ncap * 8) A.f3 A.r3
  obtain ⟨l4,_,_⟩ := alloc_step_layout p4 (ncap * 8) A.f4 A.r4
  rw [← A.e1] at l0 a1
  rw [← A.e2] at l1 a2
  rw [← A.e3] at l2 a3
  rw [← A.e4] at l3 a4
  rw [← A.e5] at l4
  rw [keysSize] at l0
  rw [eightSize] at l1 l3 l4
  have f5 := A.f5
  have tFits : table.toNat + 72 < 2 ^ 64 := by omega
  have hdr : ∀ k : Nat, k ≤ 64 → (table + BitVec.ofNat 64 k).toNat = table.toNat + k :=
    fun k hk => word_add_toNat table k (by omega)
  have ne : ∀ i j : Nat, i ≤ 64 → j ≤ 64 → i ≠ j → table + BitVec.ofNat 64 i ≠ table + BitVec.ofNat 64 j :=
    fun i j hi hj h => header_ne table tFits i j hi hj h
  have cell : ∀ k : Nat, k ≤ 64 → k ≠ 16 → k ≠ 32 → k ≠ 40 → k ≠ 48 → k ≠ 56 → k ≠ 64 → k ≠ 24 →
      w7.memory (table + BitVec.ofNat 64 k) = s.memory (table + BitVec.ofNat 64 k) := by
    intro k hk e16 e32 e40 e48 e56 e64 e24
    rw [wMemory,if_neg (by exact ne k 24 hk (by omega) e24),if_neg (by exact ne k 64 hk (by omega) e64),
      if_neg (by exact ne k 56 hk (by omega) e56),if_neg (by exact ne k 48 hk (by omega) e48),
      if_neg (by exact ne k 40 hk (by omega) e40),if_neg (by exact ne k 32 hk (by omega) e32),
      if_neg (by exact ne k 16 hk (by omega) e16)]
    apply zeroFrame
    left; rw [hdr k hk]; omega
  have byteFar : ∀ slot : BitVec 64, slot.toNat < ncap.toNat → ∀ k : Nat, k ≤ 64 →
      panByteAlignHOL (p2 + slot) ≠ table + BitVec.ofNat 64 k := by
    intro slot inside k hk
    apply word_ne_of_toNat
    rw [byteAlign_toNat,BitVec.toNat_add_of_lt (by omega),hdr k hk]
    omega
  have readSame : ∀ slot : BitVec 64, slot.toNat < ncap.toNat → hashOccupancyRead w7 p2 slot = hashOccupancyRead m p2 slot := by
    intro slot inside
    apply occupancyRead_congr_at w7 m p2 slot ?_ wAddr wBe
    rw [wMemory,if_neg (by exact byteFar slot inside 24 (by omega)),if_neg (by exact byteFar slot inside 64 (by omega)),
      if_neg (by exact byteFar slot inside 56 (by omega)),if_neg (by exact byteFar slot inside 48 (by omega)),
      if_neg (by exact byteFar slot inside 40 (by omega)),if_neg (by exact byteFar slot inside 32 (by omega)),
      if_neg (by exact byteFar slot inside 16 (by omega))]
  have n := fun i j hi hj h => (ne i j hi hj h)
  exact {
    code := wCode
    power := by rw [ncapNat,inv.power,Nat.pow_succ]
    tableAligned := inv.tableAligned
    keysAligned := p0Aligned
    strideAligned := inv.strideAligned
    valuesAligned := a1
    usedAligned := a2
    orderAligned := a3
    orderPosAligned := a4
    headerKeys := headerBelow
    headerValues := by omega
    keysBefore := by omega
    valuesBefore := by omega
    usedBefore := by omega
    orderBefore := by omega
    endBound := by omega
    fits := inv.fits
    domain := fun a h1 h2 h3 => by rw [wAddr,mAddr]; exact arena a h1 h2 (by omega)
    cell0 := (cell 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans inv.cell0
    cell8 := (cell 8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans inv.cell8
    cell16 := by
      rw [wMemory,if_neg (by exact n 16 24 (by omega) (by omega) (by omega)),if_neg (by exact n 16 64 (by omega) (by omega) (by omega)),
        if_neg (by exact n 16 56 (by omega) (by omega) (by omega)),if_neg (by exact n 16 48 (by omega) (by omega) (by omega)),
        if_neg (by exact n 16 40 (by omega) (by omega) (by omega)),if_neg (by exact n 16 32 (by omega) (by omega) (by omega)),if_pos rfl]
    cell24 := by rw [wMemory,if_pos rfl]
    cell32 := by
      rw [wMemory,if_neg (by exact n 32 24 (by omega) (by omega) (by omega)),if_neg (by exact n 32 64 (by omega) (by omega) (by omega)),
        if_neg (by exact n 32 56 (by omega) (by omega) (by omega)),if_neg (by exact n 32 48 (by omega) (by omega) (by omega)),
        if_neg (by exact n 32 40 (by omega) (by omega) (by omega)),if_pos rfl]
    cell40 := by
      rw [wMemory,if_neg (by exact n 40 24 (by omega) (by omega) (by omega)),if_neg (by exact n 40 64 (by omega) (by omega) (by omega)),
        if_neg (by exact n 40 56 (by omega) (by omega) (by omega)),if_neg (by exact n 40 48 (by omega) (by omega) (by omega)),if_pos rfl]
    cell48 := by
      rw [wMemory,if_neg (by exact n 48 24 (by omega) (by omega) (by omega)),if_neg (by exact n 48 64 (by omega) (by omega) (by omega)),
        if_neg (by exact n 48 56 (by omega) (by omega) (by omega)),if_pos rfl]
    cell56 := by
      rw [wMemory,if_neg (by exact n 56 24 (by omega) (by omega) (by omega)),if_neg (by exact n 56 64 (by omega) (by omega) (by omega)),
        if_pos rfl]
    cell64 := by rw [wMemory,if_neg (by exact n 64 24 (by omega) (by omega) (by omega)),if_pos rfl]
    agreement := by rw [hashOccupiedCount_congr ncap _ _ readSame,zocc]; rfl }

#print axioms grow_fresh_aligned_regions

theorem growTail_returned_frame_regions {F : Type} (s r post : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count ncap p0 p1 p2 p3 p4 p5 : BitVec 64) (bits : Nat)
    (v : ValueHOL 64)
    (inv : HtabRegions keyLength table keys stride capacity used values order orderPos count bits s)
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
      post.memaddrs = s.memaddrs ∧ post.be = s.be ∧ OrderInv post ncap count p2 p3 p4 ∧
      ∀ w : BitVec 64, w.toNat < p0.toNat → (w.toNat < table.toNat ∨ table.toNat + 72 ≤ w.toNat) →
        post.memory w = s.memory w := by
  have capSmall : capacity.toNat ≤ 33806089496 := by have := inv.usedEnd; omega
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
  have fresh := grow_fresh_aligned_regions s r m w7 keyLength table keys stride capacity used values order orderPos count ncap
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
  have ranked : GrowRehashRankF keyLength table p0 stride ncap p2 p1 p3 p4 count (bits + 1) e.memory e count.toNat :=
    ⟨0,by rw [← he]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],by simp,by simp,
      (eLocal _ (by decide) (by decide)).trans itemsL,(eLocal _ (by decide) (by decide)).trans tL,
      ⟨keys,(eLocal _ (by decide) (by decide)).trans keysL⟩,⟨stride,(eLocal _ (by decide) (by decide)).trans strideL⟩,
      ⟨values,(eLocal _ (by decide) (by decide)).trans valsL⟩,⟨order,(eLocal _ (by decide) (by decide)).trans orderL⟩,
      eInv,OrderInv.of_count_zero eInv,fun _ _ _ _ => rfl⟩
  have loop := growRehashLoopF_run keyLength table p0 stride ncap p2 p1 p3 p4 count (bits + 1) e.memory (by omega)
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
      obtain ⟨_,⟨K,kL,kLe,_,nL,_,_,_,_,_,lInv,lTables,lFrame⟩,_,exitCond⟩ := exitFacts rfl
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
        lTables.transfer (pm.trans rm) (pa.trans ra) (pb.trans rb),?_⟩
      intro w below outside
      have l0 := (alloc_step_layout p0 (ncap * stride) p0Inside A.r0).1
      have l1 := (alloc_step_layout p1 (ncap * 8) A.f1 A.r1).1
      rw [← A.e1] at l0
      rw [← A.e2] at l1
      have tFits : table.toNat + 72 < 2 ^ 64 := by omega
      have hdr : ∀ k : Nat, k ≤ 64 → (table + BitVec.ofNat 64 k).toNat = table.toNat + k :=
        fun k hk => word_add_toNat table k (by omega)
      have n16 : w ≠ table + 16 := word_ne_of_toNat (by rw [show (table + 16 : BitVec 64).toNat = table.toNat + 16 from hdr 16 (by omega)]; omega)
      have n24 : w ≠ table + 24 := word_ne_of_toNat (by rw [show (table + 24 : BitVec 64).toNat = table.toNat + 24 from hdr 24 (by omega)]; omega)
      have n32 : w ≠ table + 32 := word_ne_of_toNat (by rw [show (table + 32 : BitVec 64).toNat = table.toNat + 32 from hdr 32 (by omega)]; omega)
      have n40 : w ≠ table + 40 := word_ne_of_toNat (by rw [show (table + 40 : BitVec 64).toNat = table.toNat + 40 from hdr 40 (by omega)]; omega)
      have n48 : w ≠ table + 48 := word_ne_of_toNat (by rw [show (table + 48 : BitVec 64).toNat = table.toNat + 48 from hdr 48 (by omega)]; omega)
      have n56 : w ≠ table + 56 := word_ne_of_toNat (by rw [show (table + 56 : BitVec 64).toNat = table.toNat + 56 from hdr 56 (by omega)]; omega)
      have n64 : w ≠ table + 64 := word_ne_of_toNat (by rw [show (table + 64 : BitVec 64).toNat = table.toNat + 64 from hdr 64 (by omega)]; omega)
      rw [pm,rm,lFrame w n24 (by omega) (by omega),← he]
      change w7.memory w = _
      rw [wMemory,if_neg n24,if_neg n64,if_neg n56,if_neg n48,if_neg n40,if_neg n32,if_neg n16]
      exact zeroFrame w (Or.inl (by omega))

#print axioms growTail_returned_frame_regions

set_option maxHeartbeats 1000000 in
theorem htabGrow_returned_frame_regions {F : Type} (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (keyLength table keys stride capacity used values order orderPos count pointer : BitVec 64) (bits : Nat)
    (inv : HtabRegions keyLength table keys stride capacity used values order orderPos count bits state)
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
        post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ OrderInv post (capacity * 2) count used' order' orderPos' ∧
        (∀ w : BitVec 64, w.toNat < pointer.toNat → (w.toNat < table.toNat ∨ table.toNat + 72 ≤ w.toNat) → post.memory w = state.memory w) ∧
        pointer.toNat ≤ keys'.toNat ∧ pointer.toNat ≤ values'.toNat := by
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
  obtain ⟨tailInv,tailAddr,tailBe,tailTables,tailFrame⟩ := growTail_returned_frame_regions s7 r inner keyLength table keys stride capacity used values order
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
    tailTables.transfer postMem postAddr postBe,fun w below outside => by rw [postMem,tailFrame w below outside,s7Facts.1],
    le_refl _,by
      have l0 := (alloc_step_layout pointer ((capacity * 2) * stride) pointerInside A.r0).1
      rw [← A.e1] at l0
      omega⟩

#print axioms htabGrow_returned_frame_regions

theorem runBounded_htabGrow_call_regions {F : Type} (state : PanSemStateFiniteExact 64 F) (tableArgument : ExpHOL 64)
    (keyLength table keys stride capacity used values order orderPos count pointer : BitVec 64) (bits : Nat)
    (inv : HtabRegions keyLength table keys stride capacity used values order orderPos count bits state)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [tableArgument] =
      some [.val (.word table)])
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerAligned : pointer.toNat % 8 = 0) (headerBelow : table.toNat + 72 ≤ pointer.toNat)
    (pointerInside : pointer.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → table.toNat ≤ a.toNat → a.toNat < 33806089496 → state.memaddrs a)
    (room : count.toNat < capacity.toNat) (small : keyLength.toNat ≤ 33806089496)
    (budget : growBodyCost keyLength capacity count + 1 ≤ state.clock) :
    RunBounded state (.call (some (none,none)) (ofString "htab_grow") [tableArgument]) (growBodyCost keyLength capacity count + 1) := by
  refine RunBounded.call args budget ?_
  intro body locals returnShape lookup
  rw [htabGrow_installed state table inv.code] at lookup
  cases lookup
  exact evaluate_htabGrow_body_bounded_regions _ keyLength table keys stride capacity used values order orderPos count pointer bits
    (inv.transfer rfl rfl rfl rfl) (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by exact heap) pointerAligned headerBelow pointerInside (fun a h1 h2 h3 => by exact arena a h1 h2 h3) room small
    (by change _ ≤ state.clock - 1; omega)

#print axioms runBounded_htabGrow_call_regions

theorem htabGrow_call_normal_frame_regions {F : Type} (state post : PanSemStateFiniteExact 64 F) (tableArgument : ExpHOL 64)
    (keyLength table keys stride capacity used values order orderPos count pointer : BitVec 64) (bits : Nat)
    (inv : HtabRegions keyLength table keys stride capacity used values order orderPos count bits state)
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
      OrderInv post (capacity * 2) count used' order' orderPos' ∧ pointer.toNat ≤ keys'.toNat ∧ pointer.toNat ≤ values'.toNat) ∧
      post.locals = state.locals ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ w : BitVec 64, w.toNat < pointer.toNat → (w.toNat < table.toNat ∨ table.toNat + 72 ≤ w.toNat) → post.memory w = state.memory w) := by
  obtain ⟨v,output,bodyRun,memory,locals⟩ := evaluate_discard_normal_body_memory state post (ofString "htab_grow")
    _ _ _ _ .one args (htabGrow_installed state table inv.code) run
  obtain ⟨k',u',v',o',op',outInv,outAddr,outBe,outTables,outFrame,kLe,vLe⟩ := htabGrow_returned_frame_regions
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
    outTables.transfer memory (meta'.2.1.trans outAddr.symm) (meta'.2.2.1.trans outBe.symm),kLe,vLe⟩,locals,meta'.2.1,meta'.2.2.1,
    fun w below outside => by rw [memory,outFrame w below outside]; rfl⟩

#print axioms htabGrow_call_normal_frame_regions



/-- Descending table layout of a fresh scratch table: arrays below the header in
reverse order (order positions lowest). -/
structure HtabDescending {F : Type}
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
  keysBelow : keys.toNat + capacity.toNat * stride.toNat ≤ table.toNat
  valuesBelow : values.toNat + capacity.toNat * 8 ≤ keys.toNat
  usedBelow : used.toNat + capacity.toNat ≤ values.toNat
  orderBelow : order.toNat + capacity.toNat * 8 ≤ used.toNat
  orderPosBelow : orderPos.toNat + capacity.toNat * 8 ≤ order.toNat
  tableEnd : table.toNat + 72 ≤ 33806089496
  fits : keyLength.toNat ≤ stride.toNat
  domain : ∀ address : BitVec 64, address.toNat % 8 = 0 → orderPos.toNat ≤ address.toNat →
    address.toNat < table.toNat + 72 → state.memaddrs address
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


/-- Bridge: descending (fresh scratch) tables are region tables. -/
theorem HtabDescending.toRegions {F : Type} {s : PanSemStateFiniteExact 64 F} {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat}
    (inv : HtabDescending keyLength table keys stride capacity used values order orderPos count bits s) : HtabRegions keyLength table keys stride capacity used values order orderPos count bits s := by
  have a1 := inv.keysBelow; have a2 := inv.valuesBelow; have a3 := inv.usedBelow; have a4 := inv.orderBelow
  have a5 := inv.orderPosBelow; have a6 := inv.tableEnd
  exact {
    code := inv.code, power := inv.power, tableAligned := inv.tableAligned, keysAligned := inv.keysAligned,
    strideAligned := inv.strideAligned, valuesAligned := inv.valuesAligned, usedAligned := inv.usedAligned,
    orderAligned := inv.orderAligned, orderPosAligned := inv.orderPosAligned,
    tableEnd := a6, keysEnd := by omega, valuesEnd := by omega, usedEnd := by omega, orderEnd := by omega,
    endBound := by omega,
    sepHK := by omega, sepHV := by omega, sepHU := by omega, sepHO := by omega, sepHP := by omega,
    sepKU := by omega, sepKO := by omega, sepKP := by omega, sepVU := by omega, sepVO := by omega,
    sepVP := by omega, sepUO := by omega, sepUP := by omega, sepOP := by omega,
    fits := inv.fits,
    domain := fun a h1 h2 => inv.domain a h1 (by omega) (by omega),
    cell0 := inv.cell0, cell8 := inv.cell8, cell16 := inv.cell16, cell24 := inv.cell24, cell32 := inv.cell32,
    cell40 := inv.cell40, cell48 := inv.cell48, cell56 := inv.cell56, cell64 := inv.cell64,
    agreement := inv.agreement }

theorem HtabDescending.transfer {F G : Type} {s : PanSemStateFiniteExact 64 F} {r : PanSemStateFiniteExact 64 G} {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat}
    (inv : HtabDescending keyLength table keys stride capacity used values order orderPos count bits s) (memory : r.memory = s.memory) (addresses : r.memaddrs = s.memaddrs) (endian : r.be = s.be)
    (code : r.code = s.code) : HtabDescending keyLength table keys stride capacity used values order orderPos count bits r := by
  have read : ∀ slot, hashOccupancyRead r used slot = hashOccupancyRead s used slot := by
    intro slot; unfold hashOccupancyRead; rw [memory,addresses,endian]
  exact { inv with
    code := code.trans inv.code,
    domain := fun a h1 h2 h3 => by rw [addresses]; exact inv.domain a h1 h2 h3,
    cell0 := by rw [memory]; exact inv.cell0, cell8 := by rw [memory]; exact inv.cell8,
    cell16 := by rw [memory]; exact inv.cell16, cell24 := by rw [memory]; exact inv.cell24,
    cell32 := by rw [memory]; exact inv.cell32, cell40 := by rw [memory]; exact inv.cell40,
    cell48 := by rw [memory]; exact inv.cell48, cell56 := by rw [memory]; exact inv.cell56,
    cell64 := by rw [memory]; exact inv.cell64,
    agreement := by rw [inv.agreement]; exact hashOccupiedCount_congr _ _ _ (fun slot _ => (read slot).symm) }

theorem HtabDescending.header_domain {F : Type} {s : PanSemStateFiniteExact 64 F} {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat}
    (inv : HtabDescending keyLength table keys stride capacity used values order orderPos count bits s) (k : Nat) (hk : k ≤ 64) (ha : k % 8 = 0) : s.memaddrs (table + BitVec.ofNat 64 k) := by
  have te := inv.tableEnd; have := inv.keysBelow; have := inv.valuesBelow; have := inv.usedBelow
  have := inv.orderBelow; have := inv.orderPosBelow
  have eq := word_add_toNat table k (by omega)
  have := inv.tableAligned
  exact inv.domain _ (by rw [eq]; omega) (by rw [eq]; omega) (by rw [eq]; omega)

theorem HtabDescending.slot_toNat {F : Type} {s : PanSemStateFiniteExact 64 F} {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat}
    (inv : HtabDescending keyLength table keys stride capacity used values order orderPos count bits s) (q : BitVec 64) (inside : q.toNat < capacity.toNat) :
    (values + q * 8).toNat = values.toNat + q.toNat * 8 ∧ (order + q * 8).toNat = order.toNat + q.toNat * 8 ∧
      (orderPos + q * 8).toNat = orderPos.toNat + q.toNat * 8 ∧
      (keys + q * stride).toNat = keys.toNat + q.toNat * stride.toNat ∧
      q.toNat * stride.toNat + stride.toNat ≤ capacity.toNat * stride.toNat :=
  inv.toRegions.slot_toNat q inside

theorem HtabDescending.write_outside {F : Type} {s : PanSemStateFiniteExact 64 F} {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat}
    (inv : HtabDescending keyLength table keys stride capacity used values order orderPos count bits s) (address value : BitVec 64)
    (header : ∀ k : Nat, k ≤ 64 → address ≠ table + BitVec.ofNat 64 k)
    (occupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → address ≠ panByteAlignHOL (used + slot)) :
    HtabDescending keyLength table keys stride capacity used values order orderPos count bits (sourceWriteWord s address value) := by
  have keep : ∀ k : Nat, k ≤ 64 → (sourceWriteWord s address value).memory (table + BitVec.ofNat 64 k) =
      s.memory (table + BitVec.ofNat 64 k) := by
    intro k hk; simp only [sourceWriteWord]; rw [if_neg (Ne.symm (header k hk))]
  have read : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      hashOccupancyRead (sourceWriteWord s address value) used slot = hashOccupancyRead s used slot := by
    intro slot inside
    exact occupancyRead_congr_at _ s used slot (by simp only [sourceWriteWord]; rw [if_neg (Ne.symm (occupancy slot inside))]) rfl rfl
  exact { inv with
    domain := fun a h1 h2 h3 => inv.domain a h1 h2 h3,
    cell0 := (keep 0 (by omega)).trans inv.cell0, cell8 := (keep 8 (by omega)).trans inv.cell8,
    cell16 := (keep 16 (by omega)).trans inv.cell16, cell24 := (keep 24 (by omega)).trans inv.cell24,
    cell32 := (keep 32 (by omega)).trans inv.cell32, cell40 := (keep 40 (by omega)).trans inv.cell40,
    cell48 := (keep 48 (by omega)).trans inv.cell48, cell56 := (keep 56 (by omega)).trans inv.cell56,
    cell64 := (keep 64 (by omega)).trans inv.cell64,
    agreement := by rw [inv.agreement]; exact hashOccupiedCount_congr _ _ _ (fun slot inside => (read slot inside).symm) }

#print axioms HtabDescending.toRegions
#print axioms HtabDescending.transfer
#print axioms HtabDescending.header_domain
#print axioms HtabDescending.write_outside
set_option maxHeartbeats 1000000 in
theorem htabInsertRaw_returned_desc {F : Type} (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (table key value keyLength keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (inv : HtabDescending keyLength table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (tables : OrderInv state capacity count used order orderPos)
    (room : count.toNat < capacity.toNat) (small : keyLength.toNat ≤ 33806089496)
    (budget : keyLength.toNat / 8 + 8 + 1 +
      (capacity.toNat * (0 + 1) + (keyLength.toNat / 32 + keyLength.toNat / 8 + 11 + 0)) ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_insert_raw) = (some (.returned v),post)) :
    HtabDescending keyLength table keys stride capacity used values order orderPos (count + 1) bits post ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ watched : BitVec 64, (watched.toNat < orderPos.toNat ∨ table.toNat + 72 ≤ watched.toNat) →
        post.memory watched = state.memory watched) ∧ OrderInv post capacity (count + 1) used order orderPos ∧
      ∀ w : BitVec 64, w ≠ table + 24 → (w.toNat < orderPos.toNat ∨
        keys.toNat + capacity.toNat * stride.toNat ≤ w.toNat) → post.memory w = state.memory w := by
  have dK := inv.keysBelow; have dV := inv.valuesBelow; have dU := inv.usedBelow; have dO := inv.orderBelow
  have dP := inv.orderPosBelow; have dT := inv.tableEnd
  have capPos : 0 < capacity.toNat := by rw [inv.power]; exact Nat.two_pow_pos bits
  have tableFits : table.toNat + 72 < 2 ^ 64 := by have := inv.keysBelow; have := keys.isLt; omega
  have header : ∀ k : Nat, k ≤ 64 → (table + BitVec.ofNat 64 k).toNat = table.toNat + k :=
    fun k hk => word_add_toNat table k (by omega)
  have headerDomain : ∀ k : Nat, k ≤ 64 → k % 8 = 0 → state.memaddrs (table + BitVec.ofNat 64 k) := by
    intro k hk ha
    apply inv.domain
    · rw [header k hk]; have := inv.tableAligned; omega
    · rw [header k hk]; omega
    · rw [header k hk]; have := inv.keysBelow; have := inv.orderBelow; have := inv.usedBelow; have := inv.orderPosBelow; omega
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
      have kb := inv.usedBelow
      have vb := inv.usedBelow
      have ub := inv.orderBelow
      have ob := inv.orderPosBelow
      have eb := inv.tableEnd
      have hk := inv.keysBelow
      have hv := inv.valuesBelow
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
          have cDomain : ∀ address : BitVec 64, address.toNat % 8 = 0 → orderPos.toNat ≤ address.toNat →
              address.toNat < table.toNat + 72 → c.memaddrs address := by
            intro address a1 a2 a3; rw [cAddr]; exact inv.domain address a1 a2 a3
          have headerMem : ∀ k : Nat, k ≤ 64 → c.memory (table + BitVec.ofNat 64 k) = state.memory (table + BitVec.ofNat 64 k) := by
            intro k hk'
            apply copyFrame
            rw [header k hk',dstNat]; omega
          have byteMem : ∀ s' : BitVec 64, s'.toNat < capacity.toNat →
              c.memory (panByteAlignHOL (used + s')) = state.memory (panByteAlignHOL (used + s')) := by
            intro s' inside'
            apply copyFrame
            rw [dstNat]; have := byteRange s' inside'; omega
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
            · rw [header k hk',dstNat]; omega
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
            keysBelow := inv.keysBelow
            valuesBelow := inv.valuesBelow
            usedBelow := inv.usedBelow
            orderBelow := inv.orderBelow
            orderPosBelow := inv.orderPosBelow
            tableEnd := inv.tableEnd
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
            postAddr,postBe,?_,?_,?_⟩
          intro watched outside
          apply untouched
          · exact word_ne_of_toNat (by rw [valueNat]; omega)
          · exact word_ne_of_toNat (by omega)
          · exact word_ne_of_toNat (by rw [orderNat]; omega)
          · exact word_ne_of_toNat (by rw [orderPosNat]; omega)
          · exact word_ne_of_toNat (by rw [h24]; omega)
          · rw [dstNat]; omega
          have kq := inv.usedBelow; have vq := inv.usedBelow; have uq := inv.orderBelow; have oq := inv.orderPosBelow
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
                (word_ne_of_toNat (by rw [qN.2.2.1,h24]; omega)) (by rw [qN.2.2.1,dstNat]; omega)]
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
                (word_ne_of_toNat (by rw [kN.2.1,h24]; omega)) (by rw [kN.2.1,dstNat]; omega)]
              exact hx
          intro w n24 far
          have := inv.usedBelow; have := inv.usedBelow; have := inv.orderBelow; have := inv.orderPosBelow
          apply untouched
          · exact word_ne_of_toNat (by rw [valueNat]; omega)
          · exact word_ne_of_toNat (by omega)
          · exact word_ne_of_toNat (by rw [orderNat]; omega)
          · exact word_ne_of_toNat (by rw [orderPosNat]; omega)
          · exact n24
          · rw [dstNat]; omega

#print axioms htabInsertRaw_returned_desc
theorem htabInsertRaw_call_normal_desc {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (table key value keyLength keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (inv : HtabDescending keyLength table keys stride capacity used values order orderPos count bits state)
    (tables : OrderInv state capacity count used order orderPos)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (room : count.toNat < capacity.toNat) (small : keyLength.toNat ≤ 33806089496)
    (budget : keyLength.toNat / 8 + 8 + 1 +
      (capacity.toNat * (0 + 1) + (keyLength.toNat / 32 + keyLength.toNat / 8 + 11 + 0)) + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_insert_raw")
      [tableArgument,keyArgument,valueArgument]) = (none,post)) :
    HtabDescending keyLength table keys stride capacity used values order orderPos (count + 1) bits post ∧
    post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
    OrderInv post capacity (count + 1) used order orderPos ∧
      ∀ w : BitVec 64, w ≠ table + 24 → (w.toNat < orderPos.toNat ∨
        keys.toNat + capacity.toNat * stride.toNat ≤ w.toNat) → post.memory w = state.memory w := by
  have dK := inv.keysBelow; have dV := inv.valuesBelow; have dU := inv.usedBelow; have dO := inv.orderBelow
  have dP := inv.orderPosBelow; have dT := inv.tableEnd
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
  have entryInv : HtabDescending keyLength table keys stride capacity used values order orderPos count bits entry :=
    inv.transfer entryMem entryAddr entryBe (by rw [← hentry]; rfl)
  obtain ⟨outInv,outAddr,outBe,_,outTables,outFine⟩ := htabInsertRaw_returned_desc entry output v table key value keyLength keys
    stride capacity used values order orderPos count bits entryInv
    (by rw [← hentry]; simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by rw [← hentry]; simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by rw [← hentry]; simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (tables.transfer entryMem entryAddr entryBe) room small (by rw [← hentry]; change _ ≤ state.clock - 1; omega) bodyRun
  have meta' := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "htab_insert_raw")
    [tableArgument,keyArgument,valueArgument])
  rw [run] at meta'
  exact ⟨outInv.transfer memory (meta'.2.1.trans (outAddr.trans entryAddr).symm)
      (meta'.2.2.1.trans (outBe.trans entryBe).symm) (meta'.1.trans (inv.code.trans outInv.code.symm)),
    meta'.2.1,meta'.2.2.1,
    outTables.transfer memory (meta'.2.1.trans (outAddr.trans entryAddr).symm)
    (meta'.2.2.1.trans (outBe.trans entryBe).symm),fun w n24 far => by rw [memory,outFine w n24 far,entryMem]⟩

#print axioms htabInsertRaw_call_normal_desc

theorem OrderInv.write_far_desc {F : Type} {s : PanSemStateFiniteExact 64 F}
    {keyLength table keys stride capacity used values order orderPos count : BitVec 64} {bits : Nat}
    (o : OrderInv s capacity count used order orderPos)
    (inv : HtabDescending keyLength table keys stride capacity used values order orderPos count bits s)
    (address value : BitVec 64)
    (occupancy : ∀ q : BitVec 64, q.toNat < capacity.toNat → address ≠ panByteAlignHOL (used + q))
    (positions : ∀ q : BitVec 64, q.toNat < capacity.toNat → address ≠ orderPos + q * 8)
    (entries : ∀ q : BitVec 64, q.toNat < capacity.toNat → address ≠ order + q * 8) :
    OrderInv (sourceWriteWord s address value) capacity count used order orderPos := by
  have dK := inv.keysBelow; have dV := inv.valuesBelow; have dU := inv.usedBelow; have dO := inv.orderBelow
  have dP := inv.orderPosBelow; have dT := inv.tableEnd
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

#print axioms OrderInv.write_far_desc

theorem runBounded_insert_tail_desc {F : Type} (g : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count key value : BitVec 64) (bits : Nat)
    (inv : HtabDescending keyLength table keys stride capacity used values order orderPos count bits g)
    (tL : g.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyL : g.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueL : g.locals.lookup (ofString "value") = some (.val (.word value)))
    (room : count.toNat < capacity.toNat) (small : keyLength.toNat ≤ 33806089496)
    (budget : insertCallCost keyLength capacity ≤ g.clock) :
    RunBounded g (.seq (.call (some (none,none)) (ofString "htab_insert_raw")
        [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")])
      (.return (.const 0))) (insertCallCost keyLength capacity + 0) := by
  have dK := inv.keysBelow; have dV := inv.valuesBelow; have dU := inv.usedBelow; have dO := inv.orderBelow
  have dP := inv.orderPosBelow; have dT := inv.tableEnd
  have args : evalListHOLFinite g (h := fun a => Classical.propDecidable (g.memaddrs a))
      [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")] =
        some [.val (.word table),.val (.word key),.val (.word value)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,tL,keyL,valueL]
  obtain ⟨empty,emptyInside,emptyRead⟩ := hashOccupiedCount_exists_empty capacity (hashOccupancyRead g used)
    (by rw [← inv.agreement]; exact room)
  refine RunBounded.seq ?_ (by omega) ?_
  · exact runBounded_htabInsertRaw_call g none _ _ _ table key value capacity keyLength stride keys used empty bits
      inv.code args (inv.header_domain 16 (by omega) (by omega)) inv.cell16
      (inv.header_domain 0 (by omega) (by omega)) inv.cell0 (inv.header_domain 8 (by omega) (by omega)) inv.cell8
      (inv.header_domain 32 (by omega) (by omega)) inv.cell32 (inv.header_domain 48 (by omega) (by omega)) inv.cell48
      inv.power emptyInside (by unfold hashOccupancyRead at emptyRead; exact emptyRead) small (by unfold insertCallCost at budget; omega)
  · intro next _ nextCode _
    exact RunBounded.ofProg (ProgBounded.straight _ (by decide)) (nextCode.trans inv.code) (Nat.zero_le _)

#print axioms runBounded_insert_tail_desc

theorem evaluate_htabSet_body_bounded_desc {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count key value pointer : BitVec 64) (bits : Nat)
    (inv : HtabDescending keyLength table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerAligned : pointer.toNat % 8 = 0) (headerBelow : table.toNat + 72 ≤ pointer.toNat)
    (pointerInside : pointer.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → table.toNat ≤ a.toNat → a.toNat < 33806089496 → state.memaddrs a)
    (room : count.toNat < capacity.toNat) (small : keyLength.toNat ≤ 33806089496)
    (budget : setBodyCost keyLength capacity count ≤ state.clock) :
    RunBounded state (sourceFunctionBody Guest.guestFn_htab_set) (setBodyCost keyLength capacity count) := by
  have dK := inv.keysBelow; have dV := inv.valuesBelow; have dU := inv.usedBelow; have dO := inv.orderBelow
  have dP := inv.orderPosBelow; have dT := inv.tableEnd
  unfold setBodyCost at budget ⊢
  rw [source_htabSet_body]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,tableLocal,keyLocal]
  refine RunBounded.decCall args budget ?_
  intro body locals returnShape lookup
  have installed : state.code.lookup (ofString "htab_find_slot") =
      some ([(ofString "t",.one),(ofString "key",.one)],sourceFunctionBody Guest.guestFn_htab_find_slot,.one) := by
    rw [inv.code]; exact originalRuntimeCode_hashFind_lookup
  rw [pan_two_word_lookup state.code.lookup (ofString "htab_find_slot") (ofString "t") (ofString "key")
    (sourceFunctionBody Guest.guestFn_htab_find_slot) table key (by decide) installed] at lookup
  cases lookup
  generalize hentry : callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update (ofString "key",.val (.word key))) = entry
  have entryFacts : entry.memory = state.memory ∧ entry.memaddrs = state.memaddrs ∧ entry.be = state.be ∧
      entry.code = state.code ∧ entry.globals = state.globals ∧ entry.clock = state.clock - 1 := by
    rw [← hentry]; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  have entryInv := inv.transfer entryFacts.1 entryFacts.2.1 entryFacts.2.2.1 entryFacts.2.2.2.1
  obtain ⟨empty,emptyInside,emptyRead⟩ := hashOccupiedCount_exists_empty capacity (hashOccupancyRead entry used)
    (by rw [← entryInv.agreement]; exact room)
  constructor
  · exact evaluate_htabFindSlot_body_bounded entry entryInv.code table key capacity keyLength stride keys used empty bits
      (by rw [← hentry]; simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      (by rw [← hentry]; simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      (entryInv.header_domain 16 (by omega) (by omega)) entryInv.cell16 (entryInv.header_domain 0 (by omega) (by omega))
      entryInv.cell0 (entryInv.header_domain 8 (by omega) (by omega)) entryInv.cell8
      (entryInv.header_domain 32 (by omega) (by omega)) entryInv.cell32 (entryInv.header_domain 48 (by omega) (by omega))
      entryInv.cell48 entryInv.power emptyInside (by unfold hashOccupancyRead at emptyRead; exact emptyRead) small
      (by rw [entryFacts.2.2.2.2.2]; omega)
  · intro v post run tc
    have frame := htabFindSlot_memoryFrame entry entryInv.code
    have meta' := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_htab_find_slot)
    rw [run] at frame meta'
    generalize hr : setVarHOLFinite (ofString "i") v { post with locals := state.locals } = r
    have rFacts : r.memory = state.memory ∧ r.memaddrs = state.memaddrs ∧ r.be = state.be ∧ r.code = state.code ∧
        r.globals = state.globals ∧ r.clock = post.clock := by
      rw [← hr]
      exact ⟨frame.1.trans entryFacts.1,meta'.2.1.trans entryFacts.2.1,meta'.2.2.1.trans entryFacts.2.2.1,
        meta'.1.trans entryFacts.2.2.2.1,frame.2.trans entryFacts.2.2.2.2.1,rfl⟩
    have rLocal : ∀ k, k ≠ ofString "i" → r.locals.lookup k = state.locals.lookup k := by
      intro k ne; rw [← hr]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne]
    have rInv := inv.transfer rFacts.1 rFacts.2.1 rFacts.2.2.1 rFacts.2.2.2.1
    have rT := (rLocal _ (by decide)).trans tableLocal
    have rKey := (rLocal _ (by decide)).trans keyLocal
    have rValue := (rLocal _ (by decide)).trans valueLocal
    refine RunBounded.seq (RunBounded.ofProg (ProgBounded.straight _ htabSetUpdate_straight) rInv.code (Nat.zero_le _))
      (by omega) ?_
    intro next upd _ _
    have same := htabSetUpdate_normal r next upd
    subst same
    have growArgs : evalListHOLFinite next (h := fun a => Classical.propDecidable (next.memaddrs a))
        [.var .local (ofString "t")] = some [.val (.word table)] := by
      rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,rT]
    refine RunBounded.seq (RunBounded.ite_cases
      (runBounded_htabGrow_call_regions next _ keyLength table keys stride capacity used values order orderPos count pointer bits
        rInv.toRegions growArgs (by rw [rFacts.2.2.2.2.1]; exact heap) pointerAligned headerBelow pointerInside
        (fun a h1 h2 h3 => by rw [rFacts.2.1]; exact arena a h1 h2 h3) room small (by omega))
      (by unfold RunBounded; rw [evaluateHOLFiniteState_skip]; exact ⟨Nat.le_add_right _ _,le_refl _,by simp⟩))
      (by omega) ?_
    intro g guardRun gCode gBudget
    have capDouble : (capacity * 2).toNat = capacity.toNat * 2 :=
      BitVec.toNat_mul_of_lt (by
        have := inv.orderBelow; have := inv.orderPosBelow; have := inv.tableEnd; change capacity.toNat * 2 < 2 ^ 64; omega)
    rcases ite_normal_cases next g _ _ _ guardRun with grown | skipped
    · obtain ⟨⟨k',u',v',o',op',gInv,_,_,_⟩,gLocals,_,_,_⟩ := htabGrow_call_normal_frame_regions next g _ keyLength table keys stride
        capacity used values order orderPos count pointer bits rInv.toRegions growArgs (by rw [rFacts.2.2.2.2.1]; exact heap)
        pointerAligned headerBelow pointerInside (fun a h1 h2 h3 => by rw [rFacts.2.1]; exact arena a h1 h2 h3) room small
        (by omega) grown
      exact runBounded_insert_tail g keyLength table k' stride (capacity * 2) u' v' o' op' count key value (bits + 1) gInv
        (by rw [gLocals]; exact rT) (by rw [gLocals]; exact rKey) (by rw [gLocals]; exact rValue)
        (by rw [capDouble]; omega) small (by omega)
    · rw [evaluateHOLFiniteState_skip] at skipped
      obtain ⟨_,rfl⟩ := Prod.mk.inj skipped
      have doubled : capacity.toNat ≤ (capacity * 2).toNat := by rw [capDouble]; omega
      exact RunBounded.weaken (runBounded_insert_tail_desc next keyLength table keys stride capacity used values order orderPos
        count key value bits rInv rT rKey rValue room small
        (by have := insertCallCost_mono keyLength capacity (capacity * 2) doubled; omega))
        (by have := insertCallCost_mono keyLength capacity (capacity * 2) doubled; omega)

#print axioms evaluate_htabSet_body_bounded_desc

set_option maxHeartbeats 2000000 in
theorem htabSet_returned_desc {F : Type} (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (keyLength table keys stride capacity used values order orderPos count key value pointer : BitVec 64) (bits : Nat)
    (inv : HtabDescending keyLength table keys stride capacity used values order orderPos count bits state)
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
      (HtabAligned keyLength table keys' stride capacity' used' values' order' orderPos' count' bits' post ∨
        HtabDescending keyLength table keys' stride capacity' used' values' order' orderPos' count' bits' post) ∧
      ((capacity' = capacity ∧ count' = count) ∨ (count'.toNat = count.toNat + 1 ∧ count'.toNat * 2 ≤ capacity'.toNat)) ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ OrderInv post capacity' count' used' order' orderPos' ∧
      (∀ w : BitVec 64, w.toNat < pointer.toNat → (w.toNat < orderPos.toNat ∨ table.toNat + 72 ≤ w.toNat) →
        post.memory w = state.memory w) := by
  have dK := inv.keysBelow; have dV := inv.valuesBelow; have dU := inv.usedBelow; have dO := inv.orderBelow
  have dP := inv.orderPosBelow; have dT := inv.tableEnd
  unfold setBodyCost at budget
  have capSmall : capacity.toNat ≤ 33806089496 := by have := inv.orderBelow; have := inv.orderPosBelow; have := inv.tableEnd; omega
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
      have hv := rInv.valuesBelow
      have vb := rInv.usedBelow
      have written := rInv.write_outside (values + wi * 8) value
        (fun k hk => word_ne_of_toNat (by
          rw [word_mul_add_toNat values wi 8 (by change _ + _ * 8 < _; have := used.isLt; omega),
            word_add_toNat table k (by have := keys.isLt; have := rInv.keysBelow; omega)]
          change ¬(_ + _ * 8 = _); omega))
        (fun slot inside => word_ne_of_toNat (by
          rw [word_mul_add_toNat values wi 8 (by change _ + _ * 8 < _; have := used.isLt; omega),byteAlign_toNat,
            BitVec.toNat_add_of_lt (by have := rInv.orderBelow; have := rInv.orderPosBelow; have := rInv.tableEnd; omega)]
          have := rInv.usedAligned
          change ¬(_ + _ * 8 = _); omega))
      have writtenTables := rTables.write_far_desc rInv (values + wi * 8) value
        (fun q inside => word_ne_of_toNat (by
          rw [word_mul_add_toNat values wi 8 (by change _ + _ * 8 < _; have := used.isLt; omega),byteAlign_toNat,
            BitVec.toNat_add_of_lt (by have := rInv.orderBelow; have := rInv.orderPosBelow; have := rInv.tableEnd; omega)]
          have := rInv.usedAligned
          change ¬(_ + _ * 8 = _); omega))
        (fun q inside => word_ne_of_toNat (by
          rw [word_mul_add_toNat values wi 8 (by change _ + _ * 8 < _; have := used.isLt; omega),
            (rInv.slot_toNat q inside).2.2.1]
          have := rInv.orderBelow; have := rInv.orderPosBelow
          change ¬(_ + _ * 8 = _); omega))
        (fun q inside => word_ne_of_toNat (by
          rw [word_mul_add_toNat values wi 8 (by change _ + _ * 8 < _; have := used.isLt; omega),
            (rInv.slot_toNat q inside).2.1]
          have := rInv.orderBelow; have := rInv.orderPosBelow
          change ¬(_ + _ * 8 = _); omega))
      refine ⟨capacity,keys,used,values,order,orderPos,count,bits,
        Or.inr (written.transfer (pm.trans um) (pa.trans ua) (pb.trans ub) (pc.trans uc)),Or.inl ⟨rfl,rfl⟩,
        pa.trans (ua.trans rFacts.2.1),pb.trans (ub.trans rFacts.2.2.1),
        writtenTables.transfer (pm.trans um) (pa.trans ua) (pb.trans ub),fun w _ outside => by
          rw [pm,um]
          simp only [sourceWriteWord]
          rw [if_neg (word_ne_of_toNat (by
            rw [word_mul_add_toNat values wi 8 (by change _ + _ * 8 < _; have := used.isLt; omega)]
            have := rInv.orderBelow; have := rInv.orderPosBelow
            change ¬(_ = _ + _ * 8); omega))]
          exact rFacts.1 ▸ rfl⟩
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
            inner.memaddrs = g.memaddrs ∧ inner.be = g.be ∧ OrderInv inner capacity' (count + 1) used' order' orderPos' ∧
            (∀ w : BitVec 64, w ≠ table + 24 → ((w.toNat < keys'.toNat ∧ w.toNat < values'.toNat) ∨
              orderPos'.toNat + capacity'.toNat * 8 ≤ w.toNat) → inner.memory w = g.memory w) := by
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
            obtain ⟨insTables,insFine⟩ := htabInsertRaw_call_normal_fine g ins _ _ _ table key value keyLength
              keys' stride capacity' used' values' order' orderPos' count bits' gInv gTables (insArgs g gl) roomG small
              (by unfold insertCallCost at gClock; omega) insRun
            obtain ⟨em,ea,eb,ec⟩ := return_const_state ins inner 0 v gRun
            exact ⟨insInv.transfer em ea eb ec,ea.trans insAddr,eb.trans insBe,insTables.transfer em ea eb,
              fun w n24 far => by rw [em]; exact insFine w n24 far⟩
      have finishD : ∀ (g : PanSemStateFiniteExact 64 F) (capacity' keys' used' values' order' orderPos' : BitVec 64)
          (bits' : Nat),
          HtabDescending keyLength table keys' stride capacity' used' values' order' orderPos' count bits' g →
          OrderInv g capacity' count used' order' orderPos' →
          g.locals = u.locals → count.toNat < capacity'.toNat →
          insertCallCost keyLength capacity' ≤ g.clock →
          evaluateHOLFiniteState g (.seq (.call (some (none,none)) (ofString "htab_insert_raw")
            [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")])
            (.return (.const 0))) = (some (.returned v),inner) →
          HtabDescending keyLength table keys' stride capacity' used' values' order' orderPos' (count + 1) bits' inner ∧
            inner.memaddrs = g.memaddrs ∧ inner.be = g.be ∧ OrderInv inner capacity' (count + 1) used' order' orderPos' ∧
            (∀ w : BitVec 64, w ≠ table + 24 → (w.toNat < orderPos'.toNat ∨
              keys'.toNat + capacity'.toNat * stride.toNat ≤ w.toNat) → inner.memory w = g.memory w) := by
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
            obtain ⟨insInv,insAddr,insBe,insTables,insFine⟩ := htabInsertRaw_call_normal_desc g ins _ _ _ table key value keyLength
              keys' stride capacity' used' values' order' orderPos' count bits' gInv gTables (insArgs g gl) roomG small
              (by unfold insertCallCost at gClock; omega) insRun
            obtain ⟨em,ea,eb,ec⟩ := return_const_state ins inner 0 v gRun
            exact ⟨insInv.transfer em ea eb ec,ea.trans insAddr,eb.trans insBe,insTables.transfer em ea eb,
              fun w n24 far => by rw [em]; exact insFine w n24 far⟩
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
            obtain ⟨⟨k',u',v',o',op',gInv,gTables,kLe,vLe⟩,gLocals,gAddr,gBe,gFrame⟩ := htabGrow_call_normal_frame_regions u g _ keyLength table keys stride
              capacity used values order orderPos count pointer bits rInv.toRegions growArgs (by rw [rFacts.2.2.2.2.1]; exact heap)
              pointerAligned headerBelow pointerInside (fun a h1 h2 h3 => by rw [rFacts.2.1]; exact arena a h1 h2 h3) room small
              (by have := rFacts.2.2.2.2.2; omega) grown
            have growB := runBounded_htabGrow_call_regions u _ keyLength table keys stride capacity used values order orderPos count
              pointer bits rInv.toRegions growArgs (by rw [rFacts.2.2.2.2.1]; exact heap) pointerAligned headerBelow pointerInside
              (fun a h1 h2 h3 => by rw [rFacts.2.1]; exact arena a h1 h2 h3) room small (by have := rFacts.2.2.2.2.2; omega)
            unfold RunBounded at growB
            rw [grown] at growB
            obtain ⟨gb1,_,_⟩ := growB
            dsimp only at gb1
            obtain ⟨fInv,fAddr,fBe,fTables,fFrame⟩ := finish g (capacity * 2) k' u' v' o' op' (bits + 1) gInv gTables gLocals (by rw [capDouble]; omega)
              (by have := rFacts.2.2.2.2.2; omega) rrun
            refine ⟨capacity * 2,k',u',v',o',op',count + 1,bits + 1,Or.inl (fInv.transfer pm pa pb pc),
              Or.inr ⟨countOne,by rw [countOne,capDouble]; omega⟩,
              pa.trans (fAddr.trans (gAddr.trans rFacts.2.1)),pb.trans (fBe.trans (gBe.trans rFacts.2.2.1)),
              fTables.transfer pm pa pb,fun w below outside => by
                have := rInv.keysBelow; have := rInv.usedBelow; have := rInv.orderBelow; have := rInv.orderPosBelow
                have h24 : (table + 24 : BitVec 64).toNat = table.toNat + 24 :=
                  word_add_toNat table 24 (by have := keys.isLt; omega)
                rw [pm,fFrame w (word_ne_of_toNat (by rw [h24]; omega)) (Or.inl ⟨by omega,by omega⟩),
                  gFrame w below (by omega),rFacts.1]⟩
          · rw [guardVal] at gcond
            simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at gcond
            have under : ¬ capacity.toNat < (count.toNat + 1) * 2 := by
              intro h; simp [h] at gcond
            rw [evaluateHOLFiniteState_skip] at skipped
            obtain ⟨_,rfl⟩ := Prod.mk.inj skipped
            have mono := insertCallCost_mono keyLength capacity (capacity * 2) (by rw [capDouble]; omega)
            obtain ⟨fInv,fAddr,fBe,fTables,fFrame⟩ := finishD u capacity keys used values order orderPos bits rInv rTables rfl room
              (by have := rFacts.2.2.2.2.2; omega) rrun
            refine ⟨capacity,keys,used,values,order,orderPos,count + 1,bits,Or.inr (fInv.transfer pm pa pb pc),
              Or.inr ⟨countOne,by rw [countOne]; omega⟩,
              pa.trans (fAddr.trans rFacts.2.1),pb.trans (fBe.trans rFacts.2.2.1),fTables.transfer pm pa pb,
              fun w _ outside => by
                have := rInv.keysBelow; have := rInv.valuesBelow; have := rInv.usedBelow; have := rInv.orderBelow
                have := rInv.orderPosBelow
                have h24 : (table + 24 : BitVec 64).toNat = table.toNat + 24 :=
                  word_add_toNat table 24 (by have := keys.isLt; omega)
                rw [pm,fFrame w (word_ne_of_toNat (by rw [h24]; omega)) (by omega),rFacts.1]⟩

#print axioms htabSet_returned_desc
theorem htabSet_call_normal_desc {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (keyLength table keys stride capacity used values order orderPos count key value pointer : BitVec 64) (bits : Nat)
    (inv : HtabDescending keyLength table keys stride capacity used values order orderPos count bits state)
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
      (HtabAligned keyLength table keys' stride capacity' used' values' order' orderPos' count' bits' post ∨
        HtabDescending keyLength table keys' stride capacity' used' values' order' orderPos' count' bits' post) ∧
      ((capacity' = capacity ∧ count' = count) ∨ (count'.toNat = count.toNat + 1 ∧ count'.toNat * 2 ≤ capacity'.toNat)) ∧
      OrderInv post capacity' count' used' order' orderPos') ∧
      post.locals = state.locals ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ w : BitVec 64, w.toNat < pointer.toNat → (w.toNat < orderPos.toNat ∨ table.toNat + 72 ≤ w.toNat) →
        post.memory w = state.memory w) := by
  have dK := inv.keysBelow; have dV := inv.valuesBelow; have dU := inv.usedBelow; have dO := inv.orderBelow
  have dP := inv.orderPosBelow; have dT := inv.tableEnd
  obtain ⟨v,output,bodyRun,memory,locals⟩ := evaluate_discard_normal_body_memory state post (ofString "htab_set")
    _ _ _ _ .one args (htabSet_installed state table key value inv.code) run
  obtain ⟨c',k',u',v',o',op',n',b',outInv,shape,outAddr,outBe,outTables,outFrame⟩ := htabSet_returned_desc
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
  exact ⟨⟨c',k',u',v',o',op',n',b',outInv.elim
      (fun a => Or.inl (a.transfer memory (meta'.2.1.trans outAddr.symm) (meta'.2.2.1.trans outBe.symm)
        (meta'.1.trans (inv.code.trans a.code.symm))))
      (fun d => Or.inr (d.transfer memory (meta'.2.1.trans outAddr.symm) (meta'.2.2.1.trans outBe.symm)
        (meta'.1.trans (inv.code.trans d.code.symm)))),shape,
    outTables.transfer memory (meta'.2.1.trans outAddr.symm) (meta'.2.2.1.trans outBe.symm)⟩,locals,meta'.2.1,meta'.2.2.1,
    fun w below outside => by rw [memory,outFrame w below outside]; rfl⟩

#print axioms htabSet_call_normal_desc

theorem runBounded_htabSet_call_desc {F : Type} (state : PanSemStateFiniteExact 64 F) (destination : Option (VarKind × MlS))
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (keyLength table keys stride capacity used values order orderPos count key value pointer : BitVec 64) (bits : Nat)
    (inv : HtabDescending keyLength table keys stride capacity used values order orderPos count bits state)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerAligned : pointer.toNat % 8 = 0) (headerBelow : table.toNat + 72 ≤ pointer.toNat)
    (pointerInside : pointer.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → table.toNat ≤ a.toNat → a.toNat < 33806089496 → state.memaddrs a)
    (room : count.toNat < capacity.toNat) (small : keyLength.toNat ≤ 33806089496)
    (budget : setBodyCost keyLength capacity count + 1 ≤ state.clock) :
    RunBounded state (.call (some (destination,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])
      (setBodyCost keyLength capacity count + 1) := by
  have dK := inv.keysBelow; have dV := inv.valuesBelow; have dU := inv.usedBelow; have dO := inv.orderBelow
  have dP := inv.orderPosBelow; have dT := inv.tableEnd
  refine RunBounded.call args budget ?_
  intro body locals returnShape lookup
  rw [htabSet_installed state table key value inv.code] at lookup
  cases lookup
  exact evaluate_htabSet_body_bounded_desc _ keyLength table keys stride capacity used values order orderPos count key value
    pointer bits (inv.transfer rfl rfl rfl rfl)
    (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by exact heap) pointerAligned headerBelow pointerInside (fun a h1 h2 h3 => by exact arena a h1 h2 h3) room small
    (by change _ ≤ state.clock - 1; omega)

#print axioms runBounded_htabSet_call_desc

set_option maxHeartbeats 1000000 in
/-- The scratch constructor yields a descending table. -/
theorem htabNewScratch_returned_desc {F : Type} (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
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
      HtabDescending keyLength pointer keys stride capacity used values order orderPos 0 bits post ∧
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
  have inv : HtabDescending keyLength pointer p1 Sd capacity p3 p2 p4 p5 0 bits post := {
    code := postCode
    power := power
    tableAligned := L1b
    keysAligned := L2b
    strideAligned := stride.2.2
    valuesAligned := L3b
    usedAligned := L4b
    orderAligned := L5b
    orderPosAligned := L6b
    keysBelow := by omega, valuesBelow := by omega, usedBelow := by omega, orderBelow := by omega,
    orderPosBelow := by omega, tableEnd := by omega
    fits := by omega
    domain := fun a h1' h2' h3' => by rw [postAddr]; exact arena a h1' (by omega) (by omega)
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
  refine ⟨pointer,p1,Sd,p3,p2,p4,p5,value,inv,OrderInv.of_count_zero_regions inv.toRegions,postAddr,postBe,L6c,L1a,fun w below => ?_⟩
  rw [postMem,x5M,if_neg (word_ne_of_toNat (by rw [t64]; omega)),x4M,if_neg (word_ne_of_toNat (by rw [t56]; omega)),
    x3M,if_neg (word_ne_of_toNat (by rw [t48]; omega)),zFrame w (by omega),x2M,
    if_neg (word_ne_of_toNat (by rw [t40]; omega)),x1M,if_neg (word_ne_of_toNat (by rw [t32]; omega)),wM,
    if_neg (word_ne_of_toNat (by rw [t24]; omega)),if_neg (word_ne_of_toNat (by rw [t16]; omega)),
    if_neg (word_ne_of_toNat (by rw [t8]; omega)),if_neg (word_ne_of_toNat (by rw [t0]; omega))]

#print axioms htabNewScratch_returned_desc
end InitECandidate.Runtime
