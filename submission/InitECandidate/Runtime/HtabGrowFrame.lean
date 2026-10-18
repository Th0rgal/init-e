import InitECandidate.Runtime.HtabGrowBound
import InitECandidate.Runtime.OriginalHashGrowCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The fresh doubled table produced by growth is aligned at count 0, from the
allocation layout, the zeroed occupancy array and the installed header. -/
theorem grow_fresh_aligned {F : Type} (s r m w7 : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count ncap p0 p1 p2 p3 p4 p5 : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits s)
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
  have capSmall : capacity.toNat ≤ 33806089496 := by have := inv.usedBefore; have := inv.orderBefore; have := inv.endBound; omega
  have ncapNat : ncap.toNat = capacity.toNat * 2 := by
    rw [ncapEq]; exact BitVec.toNat_mul_of_lt (by change capacity.toNat * 2 < 2 ^ 64; omega)
  have strideProd : capacity.toNat * stride.toNat ≤ 33806089496 := by
    have := inv.keysBefore; have := inv.usedBefore; have := inv.orderBefore; have := inv.endBound; omega
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

#print axioms grow_fresh_aligned

/-- A returned declared call, with the resumed state's globals as well. -/
theorem decCall_returned_globals {F : Type} {s post : PanSemStateFiniteExact 64 F} {name function : MlS}
    {shape : ShapeHOL} {arguments : List (ExpHOL 64)} {continuation : ProgHOL 64} {v : ValueHOL 64}
    (run : evaluateHOLFiniteState s (.decCall name shape function arguments continuation) = (some (.returned v),post)) :
    ∃ (values : List (ValueHOL 64)) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
      (returnShape : ShapeHOL) (w : ValueHOL 64) (bodyPost resumed inner : PanSemStateFiniteExact 64 F),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values ∧
      lookupCodeHOLFinite s.code.lookup function values = some (body,callee,returnShape) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned w),bodyPost) ∧
      resumed.memory = bodyPost.memory ∧ resumed.memaddrs = bodyPost.memaddrs ∧ resumed.be = bodyPost.be ∧
      resumed.code = bodyPost.code ∧ resumed.globals = bodyPost.globals ∧
      (bodyPost.clock ≤ (callEntryStateHOLFinite s callee).clock → resumed.clock = bodyPost.clock) ∧
      resumed.locals.lookup name = some w ∧
      (∀ k, k ≠ name → resumed.locals.lookup k = s.locals.lookup k) ∧
      evaluateHOLFiniteState resumed continuation = (some (.returned v),inner) ∧
      post.memory = inner.memory ∧ post.memaddrs = inner.memaddrs ∧ post.be = inner.be ∧ post.code = inner.code := by
  rw [evaluateHOLFiniteState_decCall_total] at run
  cases args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments with
  | none => rw [args] at run; simp at run
  | some values =>
    rw [args] at run
    dsimp only at run
    cases lookup : lookupCodeHOLFinite s.code.lookup function values with
    | none => rw [lookup] at run; simp at run
    | some installed =>
      obtain ⟨body,callee,returnShape⟩ := installed
      rw [lookup] at run
      dsimp only at run
      split at run
      · simp at run
      · cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk r bodyPost =>
          rw [bodyRun] at run
          dsimp only [fixClockHOLFinite] at run
          rcases r with _ | (_ | _ | _ | _ | w | _ | _)
          all_goals first
            | (simp at run; done)
            | skip
          simp only [] at run
          split at run
          · obtain ⟨e,p⟩ := Prod.mk.inj run
            refine ⟨values,body,callee,returnShape,w,bodyPost,_,_,rfl,lookup,bodyRun,?m,?a,?b,?c,?g,?k,?n,?l,Prod.ext e rfl,
              ?pm,?pa,?pb,?pc⟩
            case m => rfl
            case a => rfl
            case b => rfl
            case c => rfl
            case g => rfl
            case pm => rw [← p]
            case pa => rw [← p]
            case pb => rw [← p]
            case pc => rw [← p]
            case k =>
              intro le
              change (if _ then _ else _) = _
              rw [if_neg (by omega)]
            case n => simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
            case l =>
              intro k ne
              simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne]
          · simp at run

/-- A returned declared allocation: the continuation returned from the state
where the name holds the old heap pointer, the heap pointer advanced, memory is
unchanged and the request was safe; at most two ticks were spent before it. -/
theorem alloc_decCall_returned {F : Type} (s post : PanSemStateFiniteExact 64 F) (name : MlS) (sizeArgument : ExpHOL 64)
    (continuation : ProgHOL 64) (pointer size : BitVec 64) (v : ValueHOL 64)
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [sizeArgument] =
      some [.val (.word size)])
    (code : s.code = originalRuntimeCode)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (clock : 2 ≤ s.clock)
    (run : evaluateHOLFiniteState s (.decCall name .one (ofString "alloc") [sizeArgument] continuation) =
      (some (.returned v),post)) :
    ∃ r inner : PanSemStateFiniteExact 64 F,
      r.locals.lookup name = some (.val (.word pointer)) ∧ (∀ k, k ≠ name → r.locals.lookup k = s.locals.lookup k) ∧
      r.memory = s.memory ∧ r.memaddrs = s.memaddrs ∧ r.be = s.be ∧ r.code = s.code ∧
      r.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer size))) ∧
      size ≤ (33806089496 : BitVec 64) - pointer ∧ (allocationEnd pointer size).toNat ≤ 33806089496 ∧
      s.clock ≤ r.clock + 2 ∧
      evaluateHOLFiniteState r continuation = (some (.returned v),inner) ∧
      post.memory = inner.memory ∧ post.memaddrs = inner.memaddrs ∧ post.be = inner.be ∧ post.code = inner.code := by
  obtain ⟨values,body,callee,rs,w,bodyPost,resumed,inner,argsR,lookup,bodyRun,rm,ra,rb,rc,rg,rclk,rh,ragree,rrun,
    pm,pa,pb,pc⟩ := decCall_returned_globals run
  rw [args] at argsR
  cases argsR
  have installed : s.code.lookup (ofString "alloc") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_alloc,.one) := by
    rw [code]; exact originalRuntimeCode_allocation_lookup
  rw [pan_single_word_lookup s.code.lookup (ofString "alloc") (ofString "n")
    (sourceFunctionBody Guest.guestFn_alloc) size installed] at lookup
  cases lookup
  obtain ⟨request,finish,hw,bm,ba,bb,bc,bg⟩ := alloc_body_returned _ bodyPost pointer size (by exact code) (by exact heap)
    (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) w bodyRun
  subst hw
  have bound := evaluate_source_alloc_uniform_bounded
    (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n",.val (.word size)))) (by exact code)
    (by change 1 ≤ s.clock - 1; omega)
  rw [bodyRun] at bound
  obtain ⟨bd1,bd2,_⟩ := bound
  dsimp only at bd1 bd2
  have rClock := rclk bd2
  refine ⟨resumed,inner,rh,ragree,rm.trans bm,ra.trans ba,rb.trans bb,rc.trans bc,?_,request,finish,?_,rrun,pm,pa,pb,pc⟩
  · rw [rg,bg]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · rw [rClock]; change s.clock - 1 ≤ _ at bd1; omega

#print axioms alloc_decCall_returned

theorem growAllocs_returned {F : Type} (s post : PanSemStateFiniteExact 64 F) (tail : ProgHOL 64) (ncap stride p0 : BitVec 64)
    (v : ValueHOL 64)
    (ncapLocal : s.locals.lookup (ofString "ncap") = some (.val (.word ncap)))
    (strideLocal : s.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (code : s.code = originalRuntimeCode)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p0)))
    (clock : 10 ≤ s.clock)
    (run : evaluateHOLFiniteState s (htabGrowAllocs tail) = (some (.returned v),post)) :
    ∃ (r inner : PanSemStateFiniteExact 64 F) (p1 p2 p3 p4 p5 : BitVec 64),
      GrowAllocated s r ncap stride p0 p1 p2 p3 p4 p5 ∧ s.clock ≤ r.clock + 10 ∧
      evaluateHOLFiniteState r tail = (some (.returned v),inner) ∧
      post.memory = inner.memory ∧ post.memaddrs = inner.memaddrs ∧ post.be = inner.be ∧ post.code = inner.code := by
  unfold htabGrowAllocs at run
  obtain ⟨r1,i1,n1,o1,m1,a1,b1,c1,h1,q1,f1,k1,run1,pm1,pa1,pb1,pc1⟩ := alloc_decCall_returned s post _ _ _ p0 (ncap * stride) v
    (eval_mul_local_local s _ _ ncap stride ncapLocal strideLocal) code heap (by omega) run
  have ncap1 : r1.locals.lookup (ofString "ncap") = some (.val (.word ncap)) := (o1 _ (by decide)).trans ncapLocal
  obtain ⟨r2,i2,n2,o2,m2,a2,b2,c2,h2,q2,f2,k2,run2,pm2,pa2,pb2,pc2⟩ := alloc_decCall_returned r1 i1 _ _ _ _ (ncap * 8) v
    (eval_mul_local_const r1 _ ncap 8 ncap1) (c1.trans code) h1 (by omega) run1
  have ncap2 : r2.locals.lookup (ofString "ncap") = some (.val (.word ncap)) := (o2 _ (by decide)).trans ncap1
  obtain ⟨r3,i3,n3,o3,m3,a3,b3,c3,h3,q3,f3,k3,run3,pm3,pa3,pb3,pc3⟩ := alloc_decCall_returned r2 i2 _ _ _ _ ncap v
    (eval_local_single r2 _ ncap ncap2) ((c2.trans c1).trans code) h2 (by omega) run2
  have ncap3 : r3.locals.lookup (ofString "ncap") = some (.val (.word ncap)) := (o3 _ (by decide)).trans ncap2
  obtain ⟨r4,i4,n4,o4,m4,a4,b4,c4,h4,q4,f4,k4,run4,pm4,pa4,pb4,pc4⟩ := alloc_decCall_returned r3 i3 _ _ _ _ (ncap * 8) v
    (eval_mul_local_const r3 _ ncap 8 ncap3) ((c3.trans (c2.trans c1)).trans code) h3 (by omega) run3
  have ncap4 : r4.locals.lookup (ofString "ncap") = some (.val (.word ncap)) := (o4 _ (by decide)).trans ncap3
  obtain ⟨r5,i5,n5,o5,m5,a5,b5,c5,h5,q5,f5,k5,run5,pm5,pa5,pb5,pc5⟩ := alloc_decCall_returned r4 i4 _ _ _ _ (ncap * 8) v
    (eval_mul_local_const r4 _ ncap 8 ncap4) ((c4.trans (c3.trans (c2.trans c1))).trans code) h4 (by omega) run4
  refine ⟨r5,i5,_,_,_,_,_,{
    nkeys := by rw [o5 _ (by decide),o4 _ (by decide),o3 _ (by decide),o2 _ (by decide)]; exact n1
    nvals := by rw [o5 _ (by decide),o4 _ (by decide),o3 _ (by decide)]; exact n2
    nused := by rw [o5 _ (by decide),o4 _ (by decide)]; exact n3
    norder := by rw [o5 _ (by decide)]; exact n4
    norderPos := n5
    others := by
      intro k notIn
      simp only [growAllocNames,List.mem_cons,List.mem_nil_iff,or_false,not_or] at notIn
      obtain ⟨a,b,c,d,e⟩ := notIn
      rw [o5 k e,o4 k d,o3 k c,o2 k b,o1 k a]
    memory := m5.trans (m4.trans (m3.trans (m2.trans m1)))
    memaddrs := a5.trans (a4.trans (a3.trans (a2.trans a1)))
    be := b5.trans (b4.trans (b3.trans (b2.trans b1)))
    code := c5.trans (c4.trans (c3.trans (c2.trans c1)))
    heap := h5
    e1 := rfl, e2 := rfl, e3 := rfl, e4 := rfl, e5 := rfl
    r0 := q1, r1 := q2, r2 := q3, r3 := q4, r4 := q5
    f1 := f1, f2 := f2, f3 := f3, f4 := f4, f5 := f5 },by omega,run5,
    pm1.trans (pm2.trans (pm3.trans (pm4.trans pm5))),pa1.trans (pa2.trans (pa3.trans (pa4.trans pa5))),
    pb1.trans (pb2.trans (pb3.trans (pb4.trans pb5))),pc1.trans (pc2.trans (pc3.trans (pc4.trans pc5)))⟩

#print axioms growAllocs_returned

theorem rehashBody_not_returned {F : Type} (s post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (run : evaluateHOLFiniteState s hashGrowRehashBody = (some (.returned v),post)) : False := by
  unfold hashGrowRehashBody at run
  obtain ⟨iv,_,_,inner,_,_,_,_⟩ := dec_returned_state run
  rw [evaluateHOLFiniteState_seq_line780] at inner
  cases callRun : evaluateHOLFiniteState (setVarHOLFinite (ofString "i") iv s) (.call (some (none,none)) (ofString "htab_insert_raw")
      [.var .local (ofString "t"),
       .op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "i"),.var .local (ofString "stride")]],
       .load .one (hashOrderAddress (ofString "vals") (ofString "i"))]) with
  | mk r mid =>
    rw [callRun] at inner
    cases r with
    | none =>
      simp only at inner
      rw [evaluateHOLFiniteState_assign] at inner
      split at inner <;> (try split at inner) <;> simp at inner
    | some r =>
      obtain ⟨e,_⟩ := Prod.mk.inj inner
      have := discard_call_not_returned (setVarHOLFinite (ofString "i") iv s) (ofString "htab_insert_raw")
        [.var .local (ofString "t"),
         .op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "i"),.var .local (ofString "stride")]],
         .load .one (hashOrderAddress (ofString "vals") (ofString "i"))] v
      rw [callRun] at this
      exact this e

theorem rehashLoop_not_returned {F : Type} (s post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (run : evaluateHOLFiniteState s hashGrowRehashLoop = (some (.returned v),post)) : False :=
  while_returned_invariant _ hashGrowRehashBody (fun _ => True) (fun _ => False) (fun _ _ => trivial)
    (fun t w q _ r => rehashBody_not_returned t q w r) (fun _ _ _ _ => trivial) s.clock s rfl trivial v post run

theorem return_const_state {F : Type} (s post : PanSemStateFiniteExact 64 F) (k : BitVec 64) (v : ValueHOL 64)
    (run : evaluateHOLFiniteState s (.return (.const k)) = (some (.returned v),post)) :
    post.memory = s.memory ∧ post.memaddrs = s.memaddrs ∧ post.be = s.be ∧ post.code = s.code := by
  rw [evaluateHOLFiniteState_return] at run
  simp only [eval_const_word] at run
  repeat' (first | (split at run) | skip)
  all_goals (try simp only [Prod.mk.injEq] at run)
  all_goals (try obtain ⟨_,rfl⟩ := run)
  all_goals exact ⟨rfl,rfl,rfl,rfl⟩

#print axioms rehashLoop_not_returned
#print axioms return_const_state

/-- A store that is followed by a returning tail finished normally. -/
theorem store_seq_returned {F : Type} (s post : PanSemStateFiniteExact 64 F) (destination expression : ExpHOL 64)
    (address value : BitVec 64) {tail : ProgHOL 64} {v : ValueHOL 64}
    (hA : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) destination =
      some (.val (.word address)))
    (hV : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) expression =
      some (.val (.word value)))
    (run : evaluateHOLFiniteState s (.seq (.store destination expression) tail) = (some (.returned v),post)) :
    evaluateHOLFiniteState (sourceWriteWord s address value) tail = (some (.returned v),post) := by
  rw [evaluateHOLFiniteState_seq_line780] at run
  have control := (evaluate_store_control_frame s destination expression).1
  cases storeRun : evaluateHOLFiniteState s (.store destination expression) with
  | mk r w =>
    rw [storeRun] at run control
    cases r with
    | none =>
      rw [store_word_normal s w destination expression address value hA hV storeRun] at run
      exact run
    | some r =>
      simp only at control
      rcases control with e | e
      · cases e
      · cases e
        simp at run

/-- A returned growth tail (after the allocations) leaves the fresh doubled
table aligned with the original item count. -/
theorem growTail_returned {F : Type} (s r post : PanSemStateFiniteExact 64 F)
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
      post.memaddrs = s.memaddrs ∧ post.be = s.be := by
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
  have ranked : GrowRehashRank keyLength table p0 stride ncap p2 p1 p3 p4 count (bits + 1) e count.toNat :=
    ⟨0,by rw [← he]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],by simp,by simp,
      (eLocal _ (by decide) (by decide)).trans itemsL,(eLocal _ (by decide) (by decide)).trans tL,
      ⟨keys,(eLocal _ (by decide) (by decide)).trans keysL⟩,⟨stride,(eLocal _ (by decide) (by decide)).trans strideL⟩,
      ⟨values,(eLocal _ (by decide) (by decide)).trans valsL⟩,⟨order,(eLocal _ (by decide) (by decide)).trans orderL⟩,
      eInv⟩
  have loop := growRehashLoop_run keyLength table p0 stride ncap p2 p1 p3 p4 count (bits + 1) (by omega)
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
      obtain ⟨_,⟨K,kL,kLe,_,nL,_,_,_,_,_,lInv⟩,_,exitCond⟩ := exitFacts rfl
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
        (pa.trans ra).trans (lmeta.2.1.trans eAddr),(pb.trans rb).trans (lmeta.2.2.1.trans eBe)⟩

#print axioms growTail_returned

/-- A returned original growth body leaves a doubled aligned table with the
same item count (fresh arrays above the old heap pointer), keeping the address
map and endianness. -/
theorem htabGrow_returned_aligned {F : Type} (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
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
        post.memaddrs = state.memaddrs ∧ post.be = state.be := by
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
  obtain ⟨tailInv,tailAddr,tailBe⟩ := growTail_returned s7 r inner keyLength table keys stride capacity used values order
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
    postAddr.trans (tailAddr.trans s7Facts.2.1),postBe.trans (tailBe.trans s7Facts.2.2.1)⟩

#print axioms htabGrow_returned_aligned

theorem htabGrow_installed {F : Type} (state : PanSemStateFiniteExact 64 F) (table : BitVec 64)
    (code : state.code = originalRuntimeCode) :
    lookupCodeHOLFinite state.code.lookup (ofString "htab_grow") [.val (.word table)] =
      some (sourceFunctionBody Guest.guestFn_htab_grow,HolFiniteMapExact.empty.update (ofString "t",.val (.word table)),.one) :=
  pan_single_word_lookup state.code.lookup (ofString "htab_grow") (ofString "t") (sourceFunctionBody Guest.guestFn_htab_grow)
    table (by rw [code]; exact originalRuntimeCode_hashGrow_lookup)

/-- A handler-free `htab_grow` call on an aligned table costs growBodyCost + 1
in every outcome. -/
theorem runBounded_htabGrow_call {F : Type} (state : PanSemStateFiniteExact 64 F) (tableArgument : ExpHOL 64)
    (keyLength table keys stride capacity used values order orderPos count pointer : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits state)
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
  exact evaluate_htabGrow_body_bounded _ keyLength table keys stride capacity used values order orderPos count pointer bits
    (inv.transfer rfl rfl rfl rfl) (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by exact heap) pointerAligned headerBelow pointerInside (fun a h1 h2 h3 => by exact arena a h1 h2 h3) room small
    (by change _ ≤ state.clock - 1; omega)

/-- After a normally finishing `htab_grow` call on an aligned table, the table
is aligned at doubled capacity with the same count, and the caller's locals,
address map and endianness are unchanged. -/
theorem htabGrow_call_normal_aligned {F : Type} (state post : PanSemStateFiniteExact 64 F) (tableArgument : ExpHOL 64)
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
      HtabAligned keyLength table keys' stride (capacity * 2) used' values' order' orderPos' count (bits + 1) post) ∧
      post.locals = state.locals ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨v,output,bodyRun,memory,locals⟩ := evaluate_discard_normal_body_memory state post (ofString "htab_grow")
    _ _ _ _ .one args (htabGrow_installed state table inv.code) run
  obtain ⟨k',u',v',o',op',outInv,outAddr,outBe⟩ := htabGrow_returned_aligned
    (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "t",.val (.word table)))) output v keyLength table
    keys stride capacity
    used values order orderPos count pointer bits (inv.transfer rfl rfl rfl rfl)
    (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) (by exact heap)
    pointerAligned headerBelow pointerInside (fun a h1 h2 h3 => by exact arena a h1 h2 h3) room small
    (by change _ ≤ state.clock - 1; omega) bodyRun
  have meta' := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "htab_grow") [tableArgument])
  rw [run] at meta'
  refine ⟨⟨k',u',v',o',op',outInv.transfer memory (meta'.2.1.trans outAddr.symm) (meta'.2.2.1.trans outBe.symm)
    (meta'.1.trans (inv.code.trans outInv.code.symm))⟩,locals,meta'.2.1,meta'.2.2.1⟩

#print axioms runBounded_htabGrow_call
#print axioms htabGrow_call_normal_aligned
end InitECandidate.Runtime
