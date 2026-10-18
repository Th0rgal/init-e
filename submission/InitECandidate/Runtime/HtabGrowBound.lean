import InitECandidate.Runtime.HtabGrowRehash
import InitECandidate.Runtime.AllocationUniformBound
import InitECandidate.Runtime.PanSingleWordLookup
import InitECandidate.Runtime.MemzeroAlignedCallCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The seven header stores that install the fresh arrays and reset the count. -/
def htabGrowHeaderStores (tail : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (hashLocalAddress (ofString "t") 16) (.var .local (ofString "ncap")))
  (.seq (.store (hashLocalAddress (ofString "t") 32) (.var .local (ofString "nkeys")))
  (.seq (.store (hashLocalAddress (ofString "t") 40) (.var .local (ofString "nvals")))
  (.seq (.store (hashLocalAddress (ofString "t") 48) (.var .local (ofString "nused")))
  (.seq (.store (hashLocalAddress (ofString "t") 56) (.var .local (ofString "norder")))
  (.seq (.store (hashLocalAddress (ofString "t") 64) (.var .local (ofString "norder_pos")))
  (.seq (.store (hashLocalAddress (ofString "t") 24) (.const 0)) tail))))))

def htabGrowAllocs (tail : ProgHOL 64) : ProgHOL 64 :=
  .decCall (ofString "nkeys") .one (ofString "alloc") [.panop .mul [.var .local (ofString "ncap"),.var .local (ofString "stride")]]
  (.decCall (ofString "nvals") .one (ofString "alloc") [.panop .mul [.var .local (ofString "ncap"),.const 8]]
  (.decCall (ofString "nused") .one (ofString "alloc") [.var .local (ofString "ncap")]
  (.decCall (ofString "norder") .one (ofString "alloc") [.panop .mul [.var .local (ofString "ncap"),.const 8]]
  (.decCall (ofString "norder_pos") .one (ofString "alloc") [.panop .mul [.var .local (ofString "ncap"),.const 8]] tail))))

theorem source_htabGrow_body : sourceFunctionBody Guest.guestFn_htab_grow =
    .dec (ofString "cap") .one (.load .one (hashLocalAddress (ofString "t") 16))
    (.dec (ofString "stride") .one (.load .one (hashLocalAddress (ofString "t") 8))
    (.dec (ofString "keys") .one (.load .one (hashLocalAddress (ofString "t") 32))
    (.dec (ofString "vals") .one (.load .one (hashLocalAddress (ofString "t") 40))
    (.dec (ofString "order") .one (.load .one (hashLocalAddress (ofString "t") 56))
    (.dec (ofString "nitems") .one (.load .one (hashLocalAddress (ofString "t") 24))
    (.dec (ofString "ncap") .one (.panop .mul [.var .local (ofString "cap"),.const 2])
    (htabGrowAllocs
      (.seq (.call (some (none,none)) (ofString "memzero") [.var .local (ofString "nused"),.var .local (ofString "ncap")])
        (htabGrowHeaderStores
          (.dec (ofString "k") .one (.const 0) (.seq hashGrowRehashLoop (.return (.const 0))))))))))))) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl


/-- A declared allocator call on a word size costs 2 plus its continuation in
every outcome; the continuation is needed only after a returned allocation,
which bound the old heap pointer, advanced the heap pointer, kept memory, and
had a safe request. -/
theorem runBounded_alloc_decCall {F : Type} (s : PanSemStateFiniteExact 64 F) (name : MlS) (sizeArgument : ExpHOL 64)
    (continuation : ProgHOL 64) (pointer size : BitVec 64) {tailCost : Nat}
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [sizeArgument] =
      some [.val (.word size)])
    (code : s.code = originalRuntimeCode)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (budget : 1 + 1 + tailCost ≤ s.clock)
    (tail : ∀ r : PanSemStateFiniteExact 64 F,
      r.locals.lookup name = some (.val (.word pointer)) → (∀ k, k ≠ name → r.locals.lookup k = s.locals.lookup k) →
      r.memory = s.memory → r.memaddrs = s.memaddrs → r.be = s.be → r.code = s.code →
      r.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer size))) →
      size ≤ (33806089496 : BitVec 64) - pointer → (allocationEnd pointer size).toNat ≤ 33806089496 →
      tailCost ≤ r.clock → RunBounded r continuation tailCost) :
    RunBounded s (.decCall name .one (ofString "alloc") [sizeArgument] continuation) (1 + 1 + tailCost) := by
  refine RunBounded.decCall args budget ?_
  intro body locals returnShape lookup
  have installed : s.code.lookup (ofString "alloc") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_alloc,.one) := by
    rw [code]; exact originalRuntimeCode_allocation_lookup
  rw [pan_single_word_lookup s.code.lookup (ofString "alloc") (ofString "n")
    (sourceFunctionBody Guest.guestFn_alloc) size installed] at lookup
  cases lookup
  constructor
  · have bound := evaluate_source_alloc_uniform_bounded
      (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n",.val (.word size)))) (by exact code)
      (by change 1 ≤ s.clock - 1; omega)
    exact ⟨bound.1,bound.2.1,bound.2.2.1⟩
  · intro value post run tc
    obtain ⟨_,_,hv,pm,pa,pb,pc,pg⟩ := alloc_body_returned _ post pointer size (by exact code) (by exact heap)
      (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) value run
    subst hv
    have request := (alloc_body_returned _ post pointer size (by exact code) (by exact heap)
      (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) _ run).1
    have finish := (alloc_body_returned _ post pointer size (by exact code) (by exact heap)
      (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) _ run).2.1
    apply tail
    · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · intro k ne; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne]
    · exact pm
    · exact pa
    · exact pb
    · exact pc
    · change post.globals.lookup _ = _
      rw [pg]
      simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · exact request
    · exact finish
    · exact tc

#print axioms runBounded_alloc_decCall

def growAllocNames : List MlS :=
  [ofString "nkeys",ofString "nvals",ofString "nused",ofString "norder",ofString "norder_pos"]

/-- Facts after the five fresh-array allocations of growth. -/
structure GrowAllocated {F : Type} (s r : PanSemStateFiniteExact 64 F) (ncap stride p0 p1 p2 p3 p4 p5 : BitVec 64) : Prop where
  nkeys : r.locals.lookup (ofString "nkeys") = some (.val (.word p0))
  nvals : r.locals.lookup (ofString "nvals") = some (.val (.word p1))
  nused : r.locals.lookup (ofString "nused") = some (.val (.word p2))
  norder : r.locals.lookup (ofString "norder") = some (.val (.word p3))
  norderPos : r.locals.lookup (ofString "norder_pos") = some (.val (.word p4))
  others : ∀ k, k ∉ growAllocNames → r.locals.lookup k = s.locals.lookup k
  memory : r.memory = s.memory
  memaddrs : r.memaddrs = s.memaddrs
  be : r.be = s.be
  code : r.code = s.code
  heap : r.globals.lookup (ofString "heap_ptr") = some (.val (.word p5))
  e1 : p1 = allocationEnd p0 (ncap * stride)
  e2 : p2 = allocationEnd p1 (ncap * 8)
  e3 : p3 = allocationEnd p2 ncap
  e4 : p4 = allocationEnd p3 (ncap * 8)
  e5 : p5 = allocationEnd p4 (ncap * 8)
  r0 : ncap * stride ≤ (33806089496 : BitVec 64) - p0
  r1 : ncap * 8 ≤ (33806089496 : BitVec 64) - p1
  r2 : ncap ≤ (33806089496 : BitVec 64) - p2
  r3 : ncap * 8 ≤ (33806089496 : BitVec 64) - p3
  r4 : ncap * 8 ≤ (33806089496 : BitVec 64) - p4
  f1 : p1.toNat ≤ 33806089496
  f2 : p2.toNat ≤ 33806089496
  f3 : p3.toNat ≤ 33806089496
  f4 : p4.toNat ≤ 33806089496
  f5 : p5.toNat ≤ 33806089496

theorem eval_mul_local_const {F : Type} (s : PanSemStateFiniteExact 64 F) (name : MlS) (x k : BitVec 64)
    (binding : s.locals.lookup name = some (.val (.word x))) :
    evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.panop .mul [.var .local name,.const k]] =
      some [.val (.word (x * k))] := by
  rw [evalListHOLFinite_eq_toExact]
  simp [evalListHOLExact,evalHOLExact,binding,panOpHOL,valueIsWord,valueWord]

theorem eval_mul_local_local {F : Type} (s : PanSemStateFiniteExact 64 F) (a b : MlS) (x y : BitVec 64)
    (ba : s.locals.lookup a = some (.val (.word x))) (bb : s.locals.lookup b = some (.val (.word y))) :
    evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.panop .mul [.var .local a,.var .local b]] =
      some [.val (.word (x * y))] := by
  rw [evalListHOLFinite_eq_toExact]
  simp [evalListHOLExact,evalHOLExact,ba,bb,panOpHOL,valueIsWord,valueWord]

theorem eval_local_single {F : Type} (s : PanSemStateFiniteExact 64 F) (a : MlS) (x : BitVec 64)
    (ba : s.locals.lookup a = some (.val (.word x))) :
    evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.var .local a] = some [.val (.word x)] := by
  rw [evalListHOLFinite_eq_toExact]
  simp [evalListHOLExact,evalHOLExact,ba]

/-- Growth's five allocations cost 10 plus their continuation, needed only
after all five returned. -/
theorem runBounded_growAllocs {F : Type} (s : PanSemStateFiniteExact 64 F) (tail : ProgHOL 64) (ncap stride p0 : BitVec 64)
    {tailCost : Nat}
    (ncapLocal : s.locals.lookup (ofString "ncap") = some (.val (.word ncap)))
    (strideLocal : s.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (code : s.code = originalRuntimeCode)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p0)))
    (budget : 1 + 1 + (1 + 1 + (1 + 1 + (1 + 1 + (1 + 1 + tailCost)))) ≤ s.clock)
    (rest : ∀ r : PanSemStateFiniteExact 64 F, ∀ p1 p2 p3 p4 p5 : BitVec 64,
      GrowAllocated s r ncap stride p0 p1 p2 p3 p4 p5 → tailCost ≤ r.clock → RunBounded r tail tailCost) :
    RunBounded s (htabGrowAllocs tail) (1 + 1 + (1 + 1 + (1 + 1 + (1 + 1 + (1 + 1 + tailCost))))) := by
  unfold htabGrowAllocs
  apply runBounded_alloc_decCall s _ _ _ p0 (ncap * stride) (eval_mul_local_local s _ _ ncap stride ncapLocal strideLocal)
    code heap budget
  intro r1 n1 o1 m1 a1 b1 c1 h1 q1 f1 t1
  have ncap1 : r1.locals.lookup (ofString "ncap") = some (.val (.word ncap)) := (o1 _ (by decide)).trans ncapLocal
  apply runBounded_alloc_decCall r1 _ _ _ _ (ncap * 8) (eval_mul_local_const r1 _ ncap 8 ncap1) (c1.trans code) h1 t1
  intro r2 n2 o2 m2 a2 b2 c2 h2 q2 f2 t2
  have ncap2 : r2.locals.lookup (ofString "ncap") = some (.val (.word ncap)) := (o2 _ (by decide)).trans ncap1
  apply runBounded_alloc_decCall r2 _ _ _ _ ncap (eval_local_single r2 _ ncap ncap2) ((c2.trans c1).trans code) h2 t2
  intro r3 n3 o3 m3 a3 b3 c3 h3 q3 f3 t3
  have ncap3 : r3.locals.lookup (ofString "ncap") = some (.val (.word ncap)) := (o3 _ (by decide)).trans ncap2
  apply runBounded_alloc_decCall r3 _ _ _ _ (ncap * 8) (eval_mul_local_const r3 _ ncap 8 ncap3)
    ((c3.trans (c2.trans c1)).trans code) h3 t3
  intro r4 n4 o4 m4 a4 b4 c4 h4 q4 f4 t4
  have ncap4 : r4.locals.lookup (ofString "ncap") = some (.val (.word ncap)) := (o4 _ (by decide)).trans ncap3
  apply runBounded_alloc_decCall r4 _ _ _ _ (ncap * 8) (eval_mul_local_const r4 _ ncap 8 ncap4)
    ((c4.trans (c3.trans (c2.trans c1))).trans code) h4 t4
  intro r5 n5 o5 m5 a5 b5 c5 h5 q5 f5 t5
  refine rest r5 (allocationEnd p0 (ncap * stride)) (allocationEnd (allocationEnd p0 (ncap * stride)) (ncap * 8))
    (allocationEnd (allocationEnd (allocationEnd p0 (ncap * stride)) (ncap * 8)) ncap)
    (allocationEnd (allocationEnd (allocationEnd (allocationEnd p0 (ncap * stride)) (ncap * 8)) ncap) (ncap * 8))
    (allocationEnd (allocationEnd (allocationEnd (allocationEnd (allocationEnd p0 (ncap * stride)) (ncap * 8)) ncap) (ncap * 8))
      (ncap * 8)) ?_ t5
  exact {
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
    f1 := f1, f2 := f2, f3 := f3, f4 := f4, f5 := f5 }

#print axioms runBounded_growAllocs

/-- A safe request from a pointer inside the arena ends at an aligned point at
or after pointer + size. -/
theorem alloc_step_layout (pointer size : BitVec 64) (inside : pointer.toNat ≤ 33806089496)
    (request : size ≤ (33806089496 : BitVec 64) - pointer) :
    pointer.toNat + size.toNat ≤ (allocationEnd pointer size).toNat ∧
      (allocationEnd pointer size).toNat % 8 = 0 ∧ pointer.toNat + size.toNat ≤ 33806089496 := by
  have sub : ((33806089496 : BitVec 64) - pointer).toNat = 33806089496 - pointer.toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change pointer.toNat ≤ 33806089496; exact inside))]; rfl
  have le := BitVec.le_def.mp request
  rw [sub] at le
  have bounded : pointer.toNat + size.toNat ≤ 33806089496 := by omega
  have covers := allocationEnd_covers pointer size bounded
  exact ⟨covers.1,covers.2.2,bounded⟩

theorem runBounded_store_word_then {F : Type} (s : PanSemStateFiniteExact 64 F) (destination expression : ExpHOL 64)
    (address value : BitVec 64)
    (hA : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) destination =
      some (.val (.word address)))
    (hV : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) expression =
      some (.val (.word value)))
    (code : s.code = originalRuntimeCode) {tail : ProgHOL 64} {cost : Nat} (budget : cost ≤ s.clock)
    (rest : RunBounded (sourceWriteWord s address value) tail cost) :
    RunBounded s (.seq (.store destination expression) tail) (0 + cost) :=
  RunBounded.seq (RunBounded.ofProg (ProgBounded.straight _ (by simp [extStraightLine])) code (Nat.zero_le _)) (by omega)
    (fun next run _ _ => by rw [store_word_normal s next destination expression address value hA hV run]; exact rest)

theorem header_ne (table : BitVec 64) (fits : table.toNat + 72 < 2 ^ 64) (i j : Nat) (hi : i ≤ 64) (hj : j ≤ 64)
    (ne : i ≠ j) : table + BitVec.ofNat 64 i ≠ table + BitVec.ofNat 64 j :=
  word_ne_of_toNat (by rw [word_add_toNat table i (by omega),word_add_toNat table j (by omega)]; omega)

/-- A word store followed by a tail: the tail is needed only from an abstract
state that differs from the current one only by the stored cell. -/
theorem runBounded_store_step {F : Type} (s : PanSemStateFiniteExact 64 F) (destination expression : ExpHOL 64)
    (address value : BitVec 64)
    (hA : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) destination =
      some (.val (.word address)))
    (hV : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) expression =
      some (.val (.word value)))
    (code : s.code = originalRuntimeCode) {tail : ProgHOL 64} {cost : Nat} (budget : cost ≤ s.clock)
    (rest : ∀ w : PanSemStateFiniteExact 64 F, w.locals = s.locals → w.code = s.code → w.clock = s.clock →
      w.memaddrs = s.memaddrs → w.be = s.be → w.globals = s.globals →
      (∀ x, w.memory x = if x = address then .word value else s.memory x) → RunBounded w tail cost) :
    RunBounded s (.seq (.store destination expression) tail) (0 + cost) :=
  runBounded_store_word_then s destination expression address value hA hV code budget
    (rest _ rfl rfl rfl rfl rfl rfl (fun _ => rfl))

/-- Growth after the allocations: zero the fresh occupancy array, install the
new header and rehash; at most ncap + 1 + items * (insertCallCost + 1) ticks. -/
theorem runBounded_growTail {F : Type} (s r : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count ncap p0 p1 p2 p3 p4 p5 : BitVec 64) (bits : Nat)
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
    (budget : ncap.toNat + 1 + (0 + (0 + (0 + (0 + (0 + (0 + (0 +
      (count.toNat * (insertCallCost keyLength ncap + 1) + 0)))))))) ≤ r.clock) :
    RunBounded r (.seq (.call (some (none,none)) (ofString "memzero") [.var .local (ofString "nused"),.var .local (ofString "ncap")])
      (htabGrowHeaderStores (.dec (ofString "k") .one (.const 0) (.seq hashGrowRehashLoop (.return (.const 0))))))
      (ncap.toNat + 1 + (0 + (0 + (0 + (0 + (0 + (0 + (0 +
        (count.toNat * (insertCallCost keyLength ncap + 1) + 0))))))))) := by
  -- arithmetic on the old and fresh layouts
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

#print axioms runBounded_growTail

/-- Cost of the original growth body for a table of the given capacity, key
length and item count. -/
def growBodyCost (keyLength capacity count : BitVec 64) : Nat :=
  1 + 1 + (1 + 1 + (1 + 1 + (1 + 1 + (1 + 1 + ((capacity * 2).toNat + 1 + (0 + (0 + (0 + (0 + (0 + (0 + (0 +
    (count.toNat * (insertCallCost keyLength (capacity * 2) + 1) + 0)))))))))))))

/-- The original `htab_grow` body on an aligned table with count < capacity,
whose heap pointer is an aligned arena word above the header and whose arena
cells from the table up are mapped, spends at most growBodyCost ticks in every
outcome (allocation traps and memory errors included). -/
theorem evaluate_htabGrow_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count pointer : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits state)
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
  exact runBounded_growTail s7 r keyLength table keys stride capacity used values order orderPos count (capacity * 2)
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

#print axioms evaluate_htabGrow_body_bounded
end InitECandidate.Runtime
