import InitECandidate.Runtime.HtabUnionSites
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-! Heap placement of grown tables: a growth (and a set that grows) leaves the fresh order_pos array
ending at or below the post heap pointer, so later allocations cannot reach a table grown earlier.
Globals-carrying copies of the declared-call/allocation decompositions support this. -/

theorem decCall_returned_globalsG {F : Type} {s post : PanSemStateFiniteExact 64 F} {name function : MlS}
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
      post.memory = inner.memory ∧ post.memaddrs = inner.memaddrs ∧ post.be = inner.be ∧ post.code = inner.code ∧ post.globals = inner.globals := by
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
              ?pm,?pa,?pb,?pc,?pg⟩
            case m => rfl
            case a => rfl
            case b => rfl
            case c => rfl
            case g => rfl
            case pm => rw [← p]
            case pa => rw [← p]
            case pb => rw [← p]
            case pc => rw [← p]
            case pg => rw [← p]
            case k =>
              intro le
              change (if _ then _ else _) = _
              rw [if_neg (by omega)]
            case n => simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
            case l =>
              intro k ne
              simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne]
          · simp at run

#print axioms decCall_returned_globalsG

theorem alloc_decCall_returnedG {F : Type} (s post : PanSemStateFiniteExact 64 F) (name : MlS) (sizeArgument : ExpHOL 64)
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
      post.memory = inner.memory ∧ post.memaddrs = inner.memaddrs ∧ post.be = inner.be ∧ post.code = inner.code ∧ post.globals = inner.globals := by
  obtain ⟨values,body,callee,rs,w,bodyPost,resumed,inner,argsR,lookup,bodyRun,rm,ra,rb,rc,rg,rclk,rh,ragree,rrun,
    pm,pa,pb,pc,pg⟩ := decCall_returned_globalsG run
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
  refine ⟨resumed,inner,rh,ragree,rm.trans bm,ra.trans ba,rb.trans bb,rc.trans bc,?_,request,finish,?_,rrun,pm,pa,pb,pc,pg⟩
  · rw [rg,bg]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · rw [rClock]; change s.clock - 1 ≤ _ at bd1; omega

#print axioms alloc_decCall_returnedG

theorem growAllocs_returnedG {F : Type} (s post : PanSemStateFiniteExact 64 F) (tail : ProgHOL 64) (ncap stride p0 : BitVec 64)
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
      post.memory = inner.memory ∧ post.memaddrs = inner.memaddrs ∧ post.be = inner.be ∧ post.code = inner.code ∧ post.globals = inner.globals := by
  unfold htabGrowAllocs at run
  obtain ⟨r1,i1,n1,o1,m1,a1,b1,c1,h1,q1,f1,k1,run1,pm1,pa1,pb1,pc1,pg1⟩ := alloc_decCall_returnedG s post _ _ _ p0 (ncap * stride) v
    (eval_mul_local_local s _ _ ncap stride ncapLocal strideLocal) code heap (by omega) run
  have ncap1 : r1.locals.lookup (ofString "ncap") = some (.val (.word ncap)) := (o1 _ (by decide)).trans ncapLocal
  obtain ⟨r2,i2,n2,o2,m2,a2,b2,c2,h2,q2,f2,k2,run2,pm2,pa2,pb2,pc2,pg2⟩ := alloc_decCall_returnedG r1 i1 _ _ _ _ (ncap * 8) v
    (eval_mul_local_const r1 _ ncap 8 ncap1) (c1.trans code) h1 (by omega) run1
  have ncap2 : r2.locals.lookup (ofString "ncap") = some (.val (.word ncap)) := (o2 _ (by decide)).trans ncap1
  obtain ⟨r3,i3,n3,o3,m3,a3,b3,c3,h3,q3,f3,k3,run3,pm3,pa3,pb3,pc3,pg3⟩ := alloc_decCall_returnedG r2 i2 _ _ _ _ ncap v
    (eval_local_single r2 _ ncap ncap2) ((c2.trans c1).trans code) h2 (by omega) run2
  have ncap3 : r3.locals.lookup (ofString "ncap") = some (.val (.word ncap)) := (o3 _ (by decide)).trans ncap2
  obtain ⟨r4,i4,n4,o4,m4,a4,b4,c4,h4,q4,f4,k4,run4,pm4,pa4,pb4,pc4,pg4⟩ := alloc_decCall_returnedG r3 i3 _ _ _ _ (ncap * 8) v
    (eval_mul_local_const r3 _ ncap 8 ncap3) ((c3.trans (c2.trans c1)).trans code) h3 (by omega) run3
  have ncap4 : r4.locals.lookup (ofString "ncap") = some (.val (.word ncap)) := (o4 _ (by decide)).trans ncap3
  obtain ⟨r5,i5,n5,o5,m5,a5,b5,c5,h5,q5,f5,k5,run5,pm5,pa5,pb5,pc5,pg5⟩ := alloc_decCall_returnedG r4 i4 _ _ _ _ (ncap * 8) v
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
    pb1.trans (pb2.trans (pb3.trans (pb4.trans pb5))),pc1.trans (pc2.trans (pc3.trans (pc4.trans pc5))),
    pg1.trans (pg2.trans (pg3.trans (pg4.trans pg5)))⟩

#print axioms growAllocs_returnedG

/-- The growth tail (memzero, header stores, rehash loop, return) only moves the heap word upward. -/
theorem growTail_normalRel : NormalRel HeapRel (.seq (.call (some (none,none)) (ofString "memzero")
    [.var .local (ofString "nused"),.var .local (ofString "ncap")])
    (htabGrowHeaderStores (.dec (ofString "k") .one (.const 0) (.seq hashGrowRehashLoop (.return (.const 0)))))) := by
  have pre := heapRel_preorder
  apply normalRel_seq pre (normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_memzero_lookup memzero_returnedRel)
  unfold htabGrowHeaderStores
  repeat apply normalRel_seq pre (heapRel_leaf (fun _ => rfl))
  apply normalRel_dec pre
  exact normalRel_seq pre (normalRel_while pre _ rehashBody_normalRel) (heapRel_leaf (fun _ => rfl))

set_option maxHeartbeats 1000000 in
/-- Growth of a region table: the fresh order_pos array ends at or below the post heap pointer. -/
theorem htabGrow_returned_top_regions {F : Type} (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
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
        pointer.toNat ≤ keys'.toNat ∧ pointer.toNat ≤ values'.toNat ∧
        ∃ p : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) ∧
          p.toNat % 8 = 0 ∧ p.toNat ≤ 33806089496 ∧ orderPos'.toNat + (capacity * 2).toNat * 8 ≤ p.toNat := by
  unfold growBodyCost at budget
  rw [source_htabGrow_body] at run
  obtain ⟨v1,i1,e1,r1,m1,a1,b1,c1,g1⟩ := dec_returned_globals run
  rw [eval_header_load state _ table 16 capacity tableLocal (inv.header_domain 16 (by omega) (by omega)) inv.cell16] at e1
  cases e1
  obtain ⟨v2,i2,e2,r2,m2,a2,b2,c2,g2⟩ := dec_returned_globals r1
  rw [eval_header_load _ _ table 8 stride
    (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
    (by exact inv.header_domain 8 (by omega) (by omega)) (by exact inv.cell8)] at e2
  cases e2
  obtain ⟨v3,i3,e3,r3,m3,a3,b3,c3,g3⟩ := dec_returned_globals r2
  rw [eval_header_load _ _ table 32 keys
    (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
    (by exact inv.header_domain 32 (by omega) (by omega)) (by exact inv.cell32)] at e3
  cases e3
  obtain ⟨v4,i4,e4,r4,m4,a4,b4,c4,g4⟩ := dec_returned_globals r3
  rw [eval_header_load _ _ table 40 values
    (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
    (by exact inv.header_domain 40 (by omega) (by omega)) (by exact inv.cell40)] at e4
  cases e4
  obtain ⟨v5,i5,e5,r5,m5,a5,b5,c5,g5⟩ := dec_returned_globals r4
  rw [eval_header_load _ _ table 56 order
    (by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tableLocal])
    (by exact inv.header_domain 56 (by omega) (by omega)) (by exact inv.cell56)] at e5
  cases e5
  obtain ⟨v6,i6,e6,r6,m6,a6,b6,c6,g6⟩ := dec_returned_globals r5
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
  obtain ⟨v7,i7,e7,r7,m7,a7,b7,c7,g7⟩ := dec_returned_globals r6
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
  obtain ⟨r,inner,p1,p2,p3,p4,p5,A,rClock,tailRun,qm,qa,qb,qc,qg⟩ := growAllocs_returnedG s7 i7 _ (capacity * 2) stride pointer v
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
  refine ⟨pointer,p2,p1,p3,p4,tailInv.transfer postMem postAddr postBe postCode,
    postAddr.trans (tailAddr.trans s7Facts.2.1),postBe.trans (tailBe.trans s7Facts.2.2.1),
    tailTables.transfer postMem postAddr postBe,fun w below outside => by rw [postMem,tailFrame w below outside,s7Facts.1],
    le_refl _,by
      have l0 := (alloc_step_layout pointer ((capacity * 2) * stride) pointerInside A.r0).1
      rw [← A.e1] at l0
      omega,?_⟩
  have capSmall : capacity.toNat ≤ 33806089496 := by have := inv.endBound; omega
  have cap2 : (capacity * 2).toNat = capacity.toNat * 2 := BitVec.toNat_mul_of_lt (by change _ * 2 < _; omega)
  have cap28 : (capacity * 2 * 8).toNat = capacity.toNat * 2 * 8 := by
    rw [BitVec.toNat_mul_of_lt (by rw [cap2]; change _ * 8 < _; omega),cap2]; rfl
  have tailRel : HeapRel r.globals inner.globals := by
    have h := normalRel_apply growTail_normalRel (X := r) (by rw [tailRun]; exact Or.inr (Or.inr (Or.inr ⟨v,rfl⟩)))
      (by rw [A.code,s7Facts.2.2.2.1]; exact inv.code)
    rw [tailRun] at h
    exact h
  have l4 := alloc_step_layout p4 ((capacity * 2) * 8) A.f4 A.r4
  rw [← A.e5] at l4
  obtain ⟨p,hp,le,pal,pin⟩ := tailRel.2 p5 A.heap l4.2.1 A.f5
  have postG : post.globals = inner.globals :=
    g1.trans (g2.trans (g3.trans (g4.trans (g5.trans (g6.trans (g7.trans qg))))))
  refine ⟨p,by rw [postG]; exact hp,pal,pin,?_⟩
  rw [cap28] at l4
  rw [cap2]
  omega

#print axioms htabGrow_returned_top_regions

theorem htabGrow_call_top_regions {F : Type} (state post : PanSemStateFiniteExact 64 F) (tableArgument : ExpHOL 64)
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
    ∃ p : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) ∧
      p.toNat % 8 = 0 ∧ p.toNat ≤ 33806089496 ∧
      ∀ op : BitVec 64, post.memory (table + 64) = .word op → op.toNat + (capacity * 2).toNat * 8 ≤ p.toNat := by
  obtain ⟨v,output,bodyRun,pm,_,pg,_,_,_⟩ := evaluate_discard_normal_body_globals state post _ _ _ _ _ _ args
    (htabGrow_installed state table inv.code) run
  obtain ⟨k',u',v',o',op',outInv,_,_,_,_,_,_,p,hp,pal,pin,le⟩ := htabGrow_returned_top_regions
    (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "t",.val (.word table)))) output v keyLength table
    keys stride capacity used values order orderPos count pointer bits (inv.transfer rfl rfl rfl rfl)
    (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) (by exact heap)
    pointerAligned headerBelow pointerInside (fun a h1 h2 h3 => by exact arena a h1 h2 h3) room small
    (by change _ ≤ state.clock - 1; omega) bodyRun
  refine ⟨p,by rw [pg]; exact hp,pal,pin,fun op cell => ?_⟩
  have c64 := outInv.cell64
  rw [pm,show (table + 64 : BitVec 64) = table + BitVec.ofNat 64 64 from rfl] at cell
  rw [show (table + 64 : BitVec 64) = table + BitVec.ofNat 64 64 from rfl] at c64
  rw [cell] at c64
  simp only [HolWordLab.word.injEq] at c64
  subst c64
  exact le

#print axioms htabGrow_call_top_regions

/-- The insertion call and final return of set only move the heap word upward. -/
theorem setInsertTail_normalRel : NormalRel HeapRel (.seq (.call (some (none,none)) (ofString "htab_insert_raw")
    [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")]) (.return (.const 0))) :=
  normalRel_seq heapRel_preorder (normalRel_discard_call heapRel_preorder _ _ _ _ _ originalRuntimeCode_hashInsert_lookup
    (NormalRel.returned htabInsertRaw_normalRel)) (heapRel_leaf (fun _ => rfl))

set_option maxHeartbeats 1000000 in
/-- Set on an aligned table, with the fine frame (header and current array block only), the capacity bound
and the array layout outcome (unchanged arrays, or fresh arrays at or above the heap pointer). -/
theorem htabSet_returned_top {F : Type} (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
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
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ OrderInv post capacity' count' used' order' orderPos' ∧
      (capacity' = capacity ∨ capacity'.toNat < 4 * count'.toNat) ∧
      ((capacity' = capacity ∧ keys' = keys ∧ values' = values ∧ orderPos' = orderPos) ∨
        (pointer.toNat ≤ keys'.toNat ∧ pointer.toNat ≤ values'.toNat ∧
          ∃ p : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) ∧
            orderPos'.toNat + capacity'.toNat * 8 ≤ p.toNat)) ∧
      (∀ w : BitVec 64, w.toNat < pointer.toNat → (w.toNat < table.toNat ∨ table.toNat + 72 ≤ w.toNat) →
        ((w.toNat < keys.toNat ∧ w.toNat < values.toNat) ∨ orderPos.toNat + capacity.toNat * 8 ≤ w.toNat) →
        post.memory w = state.memory w) := by
  unfold setBodyCost at budget
  have capSmall : capacity.toNat ≤ 33806089496 := by have := inv.usedBefore; have := inv.orderBefore; have := inv.endBound; omega
  rw [source_htabSet_body] at run
  obtain ⟨values0,body,callee,rs,w,bodyPost,r,inner,args,lookup,bodyRun,rm,ra,rb,rc,rg,rclk,rh,ragree,rrun,
    pm,pa,pb,pc,pg⟩ := decCall_returned_globalsG run
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
        writtenTables.transfer (pm.trans um) (pa.trans ua) (pb.trans ub),Or.inl rfl,Or.inl ⟨rfl,rfl,rfl,rfl⟩,
        fun w _ _ fine => by
          rw [pm,um]
          simp only [sourceWriteWord]
          rw [if_neg (word_ne_of_toNat (by
            rw [word_mul_add_toNat values wi 8 (by change _ + _ * 8 < _; have := used.isLt; omega)]
            have := rInv.usedBefore; have := rInv.orderBefore
            change ¬(_ = _ + _ * 8); rcases fine with ⟨f1,f2⟩ | f3 <;> omega))]
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
            obtain ⟨⟨k',u',v',o',op',gInv,gTables,kLe,vLe⟩,gLocals,gAddr,gBe,gFrame⟩ := htabGrow_call_normal_frame u g _ keyLength table keys stride
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
            obtain ⟨fInv,fAddr,fBe,fTables,fFrame⟩ := finish g (capacity * 2) k' u' v' o' op' (bits + 1) gInv gTables gLocals (by rw [capDouble]; omega)
              (by have := rFacts.2.2.2.2.2; omega) rrun
            obtain ⟨gp,ghp,gpal,gpin,gtop⟩ := htabGrow_call_top_regions u g _ keyLength table keys stride
              capacity used values order orderPos count pointer bits rInv.toRegions growArgs (by rw [rFacts.2.2.2.2.1]; exact heap)
              pointerAligned headerBelow pointerInside (fun a h1 h2 h3 => by rw [rFacts.2.1]; exact arena a h1 h2 h3) room small
              (by have := rFacts.2.2.2.2.2; omega) grown
            have opTop := gtop op' gInv.cell64
            have finRel : HeapRel g.globals inner.globals := by
              have h := normalRel_apply setInsertTail_normalRel (X := g) (by rw [rrun]; exact Or.inr (Or.inr (Or.inr ⟨v,rfl⟩)))
                gInv.code
              rw [rrun] at h
              exact h
            obtain ⟨pTop,hpTop,lePTop,_,_⟩ := finRel.2 gp ghp gpal gpin
            refine ⟨capacity * 2,k',u',v',o',op',count + 1,bits + 1,fInv.transfer pm pa pb pc,
              Or.inr ⟨countOne,by rw [countOne,capDouble]; omega⟩,
              pa.trans (fAddr.trans (gAddr.trans rFacts.2.1)),pb.trans (fBe.trans (gBe.trans rFacts.2.2.1)),
              fTables.transfer pm pa pb,Or.inr (by rw [capDouble,countOne]; omega),Or.inr ⟨kLe,vLe,pTop,by rw [pg]; exact hpTop,by omega⟩,fun w below hdr _ => by
                have := rInv.headerKeys; have := rInv.keysBefore; have := rInv.usedBefore; have := rInv.orderBefore
                have h24 : (table + 24 : BitVec 64).toNat = table.toNat + 24 :=
                  word_add_toNat table 24 (by have := keys.isLt; omega)
                rw [pm,fFrame w (word_ne_of_toNat (by rw [h24]; omega)) (Or.inl ⟨by omega,by omega⟩),
                  gFrame w below hdr,rFacts.1]⟩
          · rw [guardVal] at gcond
            simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at gcond
            have under : ¬ capacity.toNat < (count.toNat + 1) * 2 := by
              intro h; simp [h] at gcond
            rw [evaluateHOLFiniteState_skip] at skipped
            obtain ⟨_,rfl⟩ := Prod.mk.inj skipped
            have mono := insertCallCost_mono keyLength capacity (capacity * 2) (by rw [capDouble]; omega)
            obtain ⟨fInv,fAddr,fBe,fTables,fFrame⟩ := finish u capacity keys used values order orderPos bits rInv rTables rfl room
              (by have := rFacts.2.2.2.2.2; omega) rrun
            refine ⟨capacity,keys,used,values,order,orderPos,count + 1,bits,fInv.transfer pm pa pb pc,
              Or.inr ⟨countOne,by rw [countOne]; omega⟩,
              pa.trans (fAddr.trans rFacts.2.1),pb.trans (fBe.trans rFacts.2.2.1),fTables.transfer pm pa pb,
              Or.inl rfl,Or.inl ⟨rfl,rfl,rfl,rfl⟩,fun w _ hdr fine => by
                have := rInv.headerKeys; have := rInv.headerValues; have := rInv.keysBefore; have := rInv.usedBefore
                have := rInv.orderBefore
                have h24 : (table + 24 : BitVec 64).toNat = table.toNat + 24 :=
                  word_add_toNat table 24 (by have := keys.isLt; omega)
                rw [pm,fFrame w (word_ne_of_toNat (by rw [h24]; omega)) fine,rFacts.1]⟩

#print axioms htabSet_returned_top


set_option maxHeartbeats 2000000 in
/-- Set on a descending scratch table: either it stays descending with the same arrays, or it grew into an
aligned table whose fresh arrays lie at or above the heap pointer; with the capacity bound. -/
theorem htabSet_returned_desc_top {F : Type} (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
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
      ((HtabDescending keyLength table keys' stride capacity' used' values' order' orderPos' count' bits' post ∧
          capacity' = capacity ∧ keys' = keys ∧ values' = values ∧ orderPos' = orderPos) ∨
        (HtabAligned keyLength table keys' stride capacity' used' values' order' orderPos' count' bits' post ∧
          pointer.toNat ≤ keys'.toNat ∧ pointer.toNat ≤ values'.toNat ∧
          ∃ p : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) ∧
            orderPos'.toNat + capacity'.toNat * 8 ≤ p.toNat)) ∧
      ((capacity' = capacity ∧ count' = count) ∨ (count'.toNat = count.toNat + 1 ∧ count'.toNat * 2 ≤ capacity'.toNat)) ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ OrderInv post capacity' count' used' order' orderPos' ∧
      (capacity' = capacity ∨ capacity'.toNat < 4 * count'.toNat) ∧
      (∀ w : BitVec 64, w.toNat < pointer.toNat → (w.toNat < orderPos.toNat ∨ table.toNat + 72 ≤ w.toNat) →
        post.memory w = state.memory w) := by
  have dK := inv.keysBelow; have dV := inv.valuesBelow; have dU := inv.usedBelow; have dO := inv.orderBelow
  have dP := inv.orderPosBelow; have dT := inv.tableEnd
  unfold setBodyCost at budget
  have capSmall : capacity.toNat ≤ 33806089496 := by have := inv.orderBelow; have := inv.orderPosBelow; have := inv.tableEnd; omega
  rw [source_htabSet_body] at run
  obtain ⟨values0,body,callee,rs,w,bodyPost,r,inner,args,lookup,bodyRun,rm,ra,rb,rc,rg,rclk,rh,ragree,rrun,
    pm,pa,pb,pc,pg⟩ := decCall_returned_globalsG run
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
        Or.inl ⟨written.transfer (pm.trans um) (pa.trans ua) (pb.trans ub) (pc.trans uc),rfl,rfl,rfl,rfl⟩,Or.inl ⟨rfl,rfl⟩,
        pa.trans (ua.trans rFacts.2.1),pb.trans (ub.trans rFacts.2.2.1),
        writtenTables.transfer (pm.trans um) (pa.trans ua) (pb.trans ub),Or.inl rfl,fun w _ outside => by
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
            obtain ⟨gp,ghp,gpal,gpin,gtop⟩ := htabGrow_call_top_regions u g _ keyLength table keys stride
              capacity used values order orderPos count pointer bits rInv.toRegions growArgs (by rw [rFacts.2.2.2.2.1]; exact heap)
              pointerAligned headerBelow pointerInside (fun a h1 h2 h3 => by rw [rFacts.2.1]; exact arena a h1 h2 h3) room small
              (by have := rFacts.2.2.2.2.2; omega) grown
            have opTop := gtop op' gInv.cell64
            have finRel : HeapRel g.globals inner.globals := by
              have h := normalRel_apply setInsertTail_normalRel (X := g) (by rw [rrun]; exact Or.inr (Or.inr (Or.inr ⟨v,rfl⟩)))
                gInv.code
              rw [rrun] at h
              exact h
            obtain ⟨pTop,hpTop,lePTop,_,_⟩ := finRel.2 gp ghp gpal gpin
            refine ⟨capacity * 2,k',u',v',o',op',count + 1,bits + 1,Or.inr ⟨fInv.transfer pm pa pb pc,kLe,vLe,pTop,by rw [pg]; exact hpTop,by omega⟩,
              Or.inr ⟨countOne,by rw [countOne,capDouble]; omega⟩,
              pa.trans (fAddr.trans (gAddr.trans rFacts.2.1)),pb.trans (fBe.trans (gBe.trans rFacts.2.2.1)),
              fTables.transfer pm pa pb,Or.inr (by rw [capDouble,countOne]; omega),fun w below outside => by
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
            refine ⟨capacity,keys,used,values,order,orderPos,count + 1,bits,Or.inl ⟨fInv.transfer pm pa pb pc,rfl,rfl,rfl,rfl⟩,
              Or.inr ⟨countOne,by rw [countOne]; omega⟩,
              pa.trans (fAddr.trans rFacts.2.1),pb.trans (fBe.trans rFacts.2.2.1),fTables.transfer pm pa pb,
              Or.inl rfl,fun w _ outside => by
                have := rInv.keysBelow; have := rInv.valuesBelow; have := rInv.usedBelow; have := rInv.orderBelow
                have := rInv.orderPosBelow
                have h24 : (table + 24 : BitVec 64).toNat = table.toNat + 24 :=
                  word_add_toNat table 24 (by have := keys.isLt; omega)
                rw [pm,fFrame w (word_ne_of_toNat (by rw [h24]; omega)) (by omega),rFacts.1]⟩

#print axioms htabSet_returned_desc_top

/-- The discarded set call on an actual (aligned or descending) table: the post table is laid out with the
same block or a block at or above the heap pointer, memory below the heap pointer outside the header and the
old block is unchanged, and the capacity grows only past a quarter of the count. -/
theorem htabSet_call_normal_laidTop {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (keyLength table keys stride capacity used values order orderPos count key value pointer : BitVec 64) (bits : Nat)
    (lo hi : Nat)
    (laid : HtabLaid keyLength table keys stride capacity used values order orderPos count bits lo hi state)
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
    (∃ (capacity' keys' used' values' order' orderPos' count' : BitVec 64) (bits' : Nat) (lo' hi' : Nat),
      HtabLaid keyLength table keys' stride capacity' used' values' order' orderPos' count' bits' lo' hi' post ∧
      OrderInv post capacity' count' used' order' orderPos' ∧
      ((capacity' = capacity ∧ count' = count) ∨ (count'.toNat = count.toNat + 1 ∧ count'.toNat * 2 ≤ capacity'.toNat)) ∧
      (capacity' = capacity ∨ capacity'.toNat < 4 * count'.toNat) ∧
      ((lo' = lo ∧ hi' = hi) ∨ (pointer.toNat ≤ lo' ∧ ∃ p : BitVec 64,
        post.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) ∧ hi' ≤ p.toNat))) ∧
      post.locals = state.locals ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ w : BitVec 64, w.toNat < pointer.toNat → (w.toNat < table.toNat ∨ table.toNat + 72 ≤ w.toNat) →
        (w.toNat < lo ∨ hi ≤ w.toNat) → post.memory w = state.memory w) := by
  obtain ⟨v,output,bodyRun,memory,locals,globalsEq,_,_,_⟩ := evaluate_discard_normal_body_globals state post (ofString "htab_set")
    _ _ _ _ .one args (htabSet_installed state table key value laid.code) run
  have meta' := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "htab_set")
    [tableArgument,keyArgument,valueArgument])
  rw [run] at meta'
  have entryT : (callEntryStateHOLFinite state (((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update
      (ofString "key",.val (.word key))).update (ofString "value",.val (.word value)))).locals.lookup (ofString "t") =
      some (.val (.word table)) := by
    simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryK : (callEntryStateHOLFinite state (((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update
      (ofString "key",.val (.word key))).update (ofString "value",.val (.word value)))).locals.lookup (ofString "key") =
      some (.val (.word key)) := by
    simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryV : (callEntryStateHOLFinite state (((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update
      (ofString "key",.val (.word key))).update (ofString "value",.val (.word value)))).locals.lookup (ofString "value") =
      some (.val (.word value)) := by
    simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  rcases laid with ⟨inv,rfl,rfl⟩ | ⟨inv,rfl,rfl⟩
  · obtain ⟨c',k',u',v',o',op',n',b',outInv,shape,outAddr,outBe,outTables,capB,layout,outFrame⟩ := htabSet_returned_top
      (callEntryStateHOLFinite state (((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update
        (ofString "key",.val (.word key))).update (ofString "value",.val (.word value)))) output v keyLength table keys stride capacity used values order orderPos count key value pointer bits
      (inv.transfer rfl rfl rfl rfl) entryT entryK entryV (by exact heap) pointerAligned headerBelow pointerInside
      (fun a h1 h2 h3 => by exact arena a h1 h2 h3) (tables.transfer rfl rfl rfl) room small
      (by change _ ≤ state.clock - 1; omega) bodyRun
    have postInv := outInv.transfer memory (meta'.2.1.trans outAddr.symm) (meta'.2.2.1.trans outBe.symm)
      (meta'.1.trans (inv.code.trans outInv.code.symm))
    refine ⟨⟨c',k',u',v',o',op',n',b',min k'.toNat v'.toNat,op'.toNat + c'.toNat * 8,Or.inl ⟨postInv,rfl,rfl⟩,
      outTables.transfer memory (meta'.2.1.trans outAddr.symm) (meta'.2.2.1.trans outBe.symm),shape,capB,?_⟩,
      locals,meta'.2.1,meta'.2.2.1,fun w below hdr outside => ?_⟩
    · rcases layout with ⟨rfl,rfl,rfl,rfl⟩ | ⟨kl,vl,pT,hpT,leT⟩
      · exact Or.inl ⟨rfl,rfl⟩
      · exact Or.inr ⟨by omega,pT,by rw [globalsEq]; exact hpT,by omega⟩
    · rw [memory,outFrame w below hdr (by omega)]; rfl
  · obtain ⟨c',k',u',v',o',op',n',b',outInv,shape,outAddr,outBe,outTables,capB,outFrame⟩ := htabSet_returned_desc_top
      (callEntryStateHOLFinite state (((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update
        (ofString "key",.val (.word key))).update (ofString "value",.val (.word value)))) output v keyLength table keys stride capacity used values order orderPos count key value pointer bits
      (inv.transfer rfl rfl rfl rfl) entryT entryK entryV (by exact heap) pointerAligned headerBelow pointerInside
      (fun a h1 h2 h3 => by exact arena a h1 h2 h3) (tables.transfer rfl rfl rfl) room small
      (by change _ ≤ state.clock - 1; omega) bodyRun
    refine ⟨?_,locals,meta'.2.1,meta'.2.2.1,fun w below _ outside => by rw [memory,outFrame w below outside]; rfl⟩
    have postTables := outTables.transfer memory (meta'.2.1.trans outAddr.symm) (meta'.2.2.1.trans outBe.symm)
    rcases outInv with ⟨d,rfl,rfl,rfl,rfl⟩ | ⟨a,kl,vl,pT,hpT,leT⟩
    · exact ⟨c',k',u',v',o',op',n',b',op'.toNat,table.toNat + 72,
        Or.inr ⟨d.transfer memory (meta'.2.1.trans outAddr.symm) (meta'.2.2.1.trans outBe.symm)
          (meta'.1.trans (inv.code.trans d.code.symm)),rfl,rfl⟩,postTables,shape,capB,Or.inl ⟨rfl,rfl⟩⟩
    · exact ⟨c',k',u',v',o',op',n',b',min k'.toNat v'.toNat,op'.toNat + c'.toNat * 8,
        Or.inl ⟨a.transfer memory (meta'.2.1.trans outAddr.symm) (meta'.2.2.1.trans outBe.symm)
          (meta'.1.trans (inv.code.trans a.code.symm)),rfl,rfl⟩,postTables,shape,capB,Or.inr ⟨by omega,pT,by rw [globalsEq]; exact hpT,by omega⟩⟩

#print axioms htabSet_call_normal_laidTop
end InitECandidate.Runtime
