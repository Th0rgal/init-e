import InitECandidate.Runtime.HtabBlockHelpers
import InitECandidate.Runtime.StateFreshTxSource
import InitECandidate.Runtime.HashNewHeaderCallHeapFrame
import InitECandidate.Runtime.HashNewCallBeforeHeader
import InitECandidate.Runtime.OriginalStateFreshTxCode
import InitECandidate.Runtime.StateFreshTxPlan
import InitECandidate.Runtime.PanNoArgsLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- `st g + o, t` for a record held in the global `g`. -/
def recPointerStore (g : MlS) (offset : Nat) : ProgHOL 64 :=
  .store (.op .add [.var .global g,.const (BitVec.ofNat 64 offset)]) (.var .local (ofString "t"))

/-- Constructor sequence `t = htab_new(w, c); st g + o, t` over a record held in the global `g`. -/
def recCtorSeq (g : MlS) : List (Nat × Nat × Nat) → ProgHOL 64 → ProgHOL 64
  | [], tail => tail
  | (width,capacity,offset) :: rest, tail =>
    .seq (.call (some (some (.local,ofString "t"),none)) (ofString "htab_new")
      [.const (BitVec.ofNat 64 width),.const (BitVec.ofNat 64 capacity)])
      (.seq (recPointerStore g offset) (recCtorSeq g rest tail))

theorem stateFreshTxConstructorSequence_eq (tail : ProgHOL 64) :
    ∀ specs, stateFreshTxConstructorSequence specs tail = recCtorSeq (ofString "ts") specs tail
  | [] => rfl
  | (w,c,o) :: rest => by
    simp only [stateFreshTxConstructorSequence,recCtorSeq,stateFreshTxPointerStore,recPointerStore,
      stateFreshTxConstructorSequence_eq tail rest]

set_option maxHeartbeats 2000000 in
/-- One block-table constructor step `t = htab_new(w, c); st bs + o, t` from an aligned heap pointer with the
full heap domain: the new table is an aligned empty table at the old heap pointer with the order invariant, its
pointer is stored at `bs + o` (below the old heap pointer), and every other word below the old heap pointer is
kept. -/
theorem rec_ctor_step {F : Type} (g : MlS) (hg : g ≠ ofString "heap_ptr") (s : PanSemStateFiniteExact 64 F) (B p : BitVec 64) (w c o bits : Nat)
    (rest : ProgHOL 64) (code : s.code = originalRuntimeCode)
    (hB : s.globals.lookup g = some (.val (.word B)))
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p))) (pal : p.toNat % 8 = 0)
    (domain : ∀ a : BitVec 64, a.toNat < 33806089496 → s.memaddrs a)
    (wB : w ≤ 52) (cB : c < 2 ^ 64) (power : c = 2 ^ bits)
    (space : p.toNat + 81 * c + 114 ≤ 33806089496) (ticks : c + 14 ≤ s.clock)
    (oldT : BitVec 64) (tL : s.locals.lookup (ofString "t") = some (.val (.word oldT)))
    (oBelow : (B + BitVec.ofNat 64 o).toNat < p.toNat) :
    ∃ (r : PanSemStateFiniteExact 64 F) (keys stride used values order orderPos p' : BitVec 64),
      evaluateHOLFiniteState s (.seq (.call (some (some (.local,ofString "t"),none)) (ofString "htab_new")
        [.const (BitVec.ofNat 64 w),.const (BitVec.ofNat 64 c)]) (.seq (recPointerStore g o) rest)) =
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
  have hB' : post.globals.lookup g = some (.val (.word B)) := by rw [rel.1 _ hg]; exact hB
  have store := evaluate_store_word post (B + BitVec.ofNat 64 o) p
    (.op .add [.var .global g,.const (BitVec.ofNat 64 o)]) (.var .local (ofString "t"))
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
  unfold recPointerStore
  rw [evaluateHOLFiniteState_seq_line780,store]

#print axioms rec_ctor_step

set_option maxHeartbeats 4000000 in
/-- The block-table constructor sequence from an aligned heap pointer above the block record: every table is
built at its record cell in constructor order between the entry and exit heap pointers, and every other word
below the entry heap pointer is kept. -/
theorem recCtorSeq_run {F : Type} (g : MlS) (hg : g ≠ ofString "heap_ptr") (B : BitVec 64) (tail : ProgHOL 64) :
    ∀ (specs : List (Nat × Nat × Nat)) (s : PanSemStateFiniteExact 64 F) (p oldT : BitVec 64), BlockPlan specs →
    s.code = originalRuntimeCode → s.globals.lookup g = some (.val (.word B)) →
    s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) → p.toNat % 8 = 0 →
    (∀ a : BitVec 64, a.toNat < 33806089496 → s.memaddrs a) → B.toNat + 80 ≤ p.toNat →
    p.toNat + stateFreshTxAllocationBudget specs ≤ 33806089496 → blockClock specs ≤ s.clock →
    s.locals.lookup (ofString "t") = some (.val (.word oldT)) →
    ∃ (post : PanSemStateFiniteExact 64 F) (P : BitVec 64),
      evaluateHOLFiniteState s (recCtorSeq g specs tail) = evaluateHOLFiniteState post tail ∧
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
      clk1,clk2⟩ := rec_ctor_step g hg s B p w c o bits (recCtorSeq g rest tail) code hB heap al domain wB cB power
        (by omega) (by omega) oldT tL (by omega)
    have bounds := stateFreshTx_next_table_bounds p w c wB cB (by omega)
    rw [← pEq] at bounds
    obtain ⟨post,P,run2,built,hP,alP,inP,leP,upP,frame2,pc,pa,pb,prel,ptl,pclk1,pclk2⟩ :=
      recCtorSeq_run g hg B tail rest r p' p plan (rc.trans code) (by rw [rrel.1 _ hg]; exact hB) hp' al'
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
    · unfold recCtorSeq; rw [run]; exact run2
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

#print axioms recCtorSeq_run


theorem blockPlan_freshRemaining : BlockPlan stateFreshTxRemainingTables :=
  BlockPlan.cons 6 (by decide) (by decide) rfl (by decide) (by decide) <|
  BlockPlan.cons 6 (by decide) (by decide) rfl (by decide) (by decide) <|
  BlockPlan.cons 4 (by decide) (by decide) rfl (by decide) (by decide) <|
  BlockPlan.cons 4 (by decide) (by decide) rfl (by decide) (by decide) <|
  BlockPlan.cons 4 (by decide) (by decide) rfl (by decide) (by decide) <|
  BlockPlan.cons 4 (by decide) (by decide) rfl (by decide) (by decide) <|
  BlockPlan.cons 4 (by decide) (by decide) rfl (by decide) (by decide) trivial

set_option maxHeartbeats 8000000 in
/-- The original `state_fresh_tx` body from an entry state with the full heap domain and room for its eight
tables: it returns 0, and every word below the entry heap pointer is unchanged (the record and all tables are
allocated at or above it). The heap ends aligned within bounds, `ts` is the entry heap pointer, `journal_n` is
reset, and all other globals are kept. -/
theorem stateFreshTx_body_memory_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer oldTs B oldCount : BitVec 64) (code : s.code = originalRuntimeCode)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (tsGlobal : s.globals.lookup (ofString "ts") = some (.val (.word oldTs)))
    (bsGlobal : s.globals.lookup (ofString "bs") = some (.val (.word B)))
    (counterGlobal : s.globals.lookup (ofString "journal_n") = some (.val (.word oldCount)))
    (reservation : pointer.toNat + 23024 ≤ 33806089496)
    (domain : ∀ a : BitVec 64, a.toNat < 33806089496 → s.memaddrs a)
    (ticks : 379 ≤ s.clock) :
    ∃ Y : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_state_fresh_tx) =
        (some (.returned (.val (.word (0 : BitVec 64)))),
          {emptyLocalsHOLFinite Y with locals := HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite Y).locals (ofString "t",s.locals.lookup (ofString "t"))}) ∧
      (∀ a : BitVec 64, a.toNat < pointer.toNat → Y.memory a = s.memory a) ∧
      Y.memaddrs = s.memaddrs ∧ Y.be = s.be ∧ Y.code = s.code ∧
      (∃ P : BitVec 64, Y.globals.lookup (ofString "heap_ptr") = some (.val (.word P)) ∧ pointer.toNat ≤ P.toNat ∧
        P.toNat % 8 = 0 ∧ P.toNat ≤ 33806089496) ∧
      Y.globals.lookup (ofString "ts") = some (.val (.word pointer)) ∧
      (∀ name, name ≠ ofString "heap_ptr" → name ≠ ofString "ts" → name ≠ ofString "journal_n" →
        Y.globals.lookup name = s.globals.lookup name) ∧
      s.clock ≤ Y.clock + 379 ∧ Y.clock ≤ s.clock := by
  have e72 : (72 : BitVec 64).toNat = 72 := rfl
  have cov := allocationEnd_covers pointer 72 (by rw [e72]; omega)
  rw [e72] at cov
  have lim : (33806089496 : BitVec 64).toNat = 33806089496 := rfl
  obtain ⟨a1,arun,aclk,amem,alocals,acode,aaddrs,abe,ats,aheap,aglob⟩ := evaluate_alloc_global_call s (.const 72) pointer 72
    oldTs (ofString "ts") (by rw [evalListHOLFinite_eq_toExact]; rfl) code (by omega) heap tsGlobal (by decide)
    (by rw [BitVec.le_def,BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)]; omega) (by omega)
  have hk : ∀ k : Nat, k < 72 → (pointer + BitVec.ofNat 64 k).toNat = pointer.toNat + k :=
    fun k h => off_toNat pointer k (by omega) (by omega)
  have e0 : (pointer + 0).toNat = pointer.toNat := hk 0 (by omega)
  have e8 : (pointer + BitVec.ofNat 64 8).toNat = pointer.toNat + 8 := hk 8 (by omega)
  have bs1 : a1.globals.lookup (ofString "bs") = some (.val (.word B)) := by rw [aglob _ (by decide) (by decide)]; exact bsGlobal
  have dom1 : ∀ a : BitVec 64, a.toNat < 33806089496 → a1.memaddrs a := by rw [aaddrs]; exact domain
  have st0 := evaluate_store_word a1 (pointer + 0) B (.op .add [.var .global (ofString "ts"),.const 0])
    (.var .global (ofString "bs")) (eval_add2 a1 _ _ _ _ (eval_global_word a1 _ pointer ats) (item_eval_const a1 _))
    (eval_global_word a1 _ B bs1) (dom1 _ (by rw [e0]; omega))
  -- the first constructor, declared
  let s2 := sourceWriteWord a1 (pointer + 0) B
  obtain ⟨p1,hp1⟩ : ∃ x : BitVec 64, x = allocationEnd pointer 72 := ⟨_,rfl⟩
  rw [← hp1] at cov aheap
  have heap2 : s2.globals.lookup (ofString "heap_ptr") = some (.val (.word p1)) := aheap
  have code2 : s2.code = originalRuntimeCode := acode.trans code
  have dom2 : ∀ a : BitVec 64, a.toNat < 33806089496 → s2.memaddrs a := dom1
  have k20 : (20 : BitVec 64).toNat ≤ 52 := by decide
  have c64 : (64 : BitVec 64).toNat = 64 := rfl
  obtain ⟨_,hdrD,wordD,byteD⟩ := htabNew_heap_domains s2 p1 20 64 k20 (by rw [c64]; omega) dom2
  have args2 : evalListHOLFinite s2 (h := fun a => Classical.propDecidable (s2.memaddrs a)) [.const 20,.const 64] =
      some [.val (.word 20),.val (.word 64)] := by rw [evalListHOLFinite_eq_toExact]; rfl
  obtain ⟨ready,rrun,_,rclk1,rclk2,rloc,rcode,raddr,rbe,rframe,decl⟩ :=
    evaluate_htabNew_call_and_declaration_before_header s2 _ _ p1 20 64 args2 code2 (by rw [c64]; change _ ≤ a1.clock; omega)
      heap2 k20 cov.2.2 (by rw [c64]; omega) hdrD wordD byteD
  obtain ⟨ready',rrun',_,_,_,_,_,_,_,rheap,_,_,_,_,_,_,_,_,_,rglob,_⟩ :=
    evaluate_htabNew_header_call_and_declaration_heap_frame s2 _ _ p1 20 64 args2 code2
      (by rw [c64]; change _ ≤ a1.clock; omega) heap2 k20 cov.2.2 (by rw [c64]; omega) hdrD wordD byteD
  rw [rrun] at rrun'
  obtain ⟨_,rfl⟩ := Prod.mk.inj rrun'
  have bounds := stateFreshTx_next_table_bounds p1 20 64 (by decide) (by decide) (by omega)
  have p2eq : allocationEnd (htabNewOrderPos p1 20 64) (64 * 8) = stateFreshTxNextTable p1 20 64 := rfl
  rw [p2eq] at rheap
  let s3 := setVarHOLFinite (ofString "t") (.val (.word p1)) ready
  have ts3 : s3.globals.lookup (ofString "ts") = some (.val (.word pointer)) := by
    change ready.globals.lookup _ = _; rw [rglob _ (by decide)]; exact ats
  have st8 := evaluate_store_word s3 (pointer + BitVec.ofNat 64 8) p1
    (.op .add [.var .global (ofString "ts"),.const (BitVec.ofNat 64 8)]) (.var .local (ofString "t"))
    (eval_add2 s3 _ _ _ _ (eval_global_word s3 _ pointer ts3) (item_eval_const s3 _))
    (item_eval_locals s3 _ p1 (by simp [s3,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]))
    (by change ready.memaddrs _; rw [raddr]; exact dom2 _ (by rw [e8]; omega))
  let s4 := sourceWriteWord s3 (pointer + BitVec.ofNat 64 8) p1
  have rb := stateFreshTx_remaining_budgets
  have bc : blockClock stateFreshTxRemainingTables = 306 := by decide
  have clk4 : blockClock stateFreshTxRemainingTables ≤ s4.clock := by
    rw [bc]; change _ ≤ ready.clock; change a1.clock ≤ ready.clock + (64 : BitVec 64).toNat + 8 at rclk1
    rw [c64] at rclk1; omega
  obtain ⟨post5,P,run5,_,hP,alP,inP,leP,_,frame5,pc5,pa5,pb5,prel5,_,clk51,clk52⟩ :=
    recCtorSeq_run (ofString "ts") (by decide) pointer (.seq (.assign .global (ofString "journal_n") (.const 0))
      (.return (.const 0))) stateFreshTxRemainingTables s4 (stateFreshTxNextTable p1 20 64) p1 blockPlan_freshRemaining
      (by change ready.code = _; rw [rcode]; exact code2) ts3 rheap bounds.2.2
      (by intro a h; change ready.memaddrs a; rw [raddr]; exact dom2 a h) (by omega)
      (by rw [rb.1]; omega) clk4
      (by simp [s4,s3,sourceWriteWord,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  -- reset and return
  have glob5 : ∀ name, name ≠ ofString "heap_ptr" → post5.globals.lookup name = s4.globals.lookup name := prel5.1
  have cnt5 : post5.globals.lookup (ofString "journal_n") = some (.val (.word oldCount)) := by
    rw [glob5 _ (by decide)]; change ready.globals.lookup _ = _; rw [rglob _ (by decide)]
    change a1.globals.lookup _ = _; rw [aglob _ (by decide) (by decide)]; exact counterGlobal
  let Y := setGlobalHOLFinite (ofString "journal_n") (.val (.word (0 : BitVec 64))) post5
  have reset : evaluateHOLFiniteState post5 (.assign .global (ofString "journal_n") (.const 0)) = (none,Y) := by
    simp [evaluateHOLFiniteState_assign,evalHOLExact,isValidValueHOLExact,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite,
      lookupKvarHOLExact,cnt5,Y]
  have finish : evaluateHOLFiniteState post5 (.seq (.assign .global (ofString "journal_n") (.const 0)) (.return (.const 0))) =
      (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite Y) := by
    rw [evaluateHOLFiniteState_seq_line780,reset]
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  have yglob : ∀ name, name ≠ ofString "journal_n" → Y.globals.lookup name = post5.globals.lookup name := by
    intro name h; simp [Y,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm h]
  have mem5 : ∀ a : BitVec 64, a.toNat < pointer.toNat → post5.memory a = s.memory a := by
    intro a lt
    have n0 : a ≠ pointer + 0 := fun e => by rw [e,e0] at lt; omega
    have n8 : a ≠ pointer + BitVec.ofNat 64 8 := fun e => by rw [e,e8] at lt; omega
    rw [frame5 a (by omega) (fun o m e => by
      have ob := BlockPlan.offsets _ blockPlan_freshRemaining o m
      rw [e,off_toNat pointer o (by omega) (by omega)] at lt; omega)]
    change (if a = pointer + BitVec.ofNat 64 8 then _ else s3.memory a) = _
    rw [if_neg n8]
    change ready.memory a = _
    rw [rframe a (by omega)]
    change (if a = pointer + 0 then _ else a1.memory a) = _
    rw [if_neg n0,amem]
  refine ⟨Y,?_,mem5,pa5.trans (raddr.trans aaddrs),pb5.trans (rbe.trans abe),
    pc5.trans (rcode.trans (acode)),⟨P,by rw [yglob _ (by decide)]; exact hP,by omega,alP,inP⟩,?_,?_,?_,?_⟩
  · rw [source_stateFreshTx_body,evaluateHOLFiniteState_seq_line780,arun]; dsimp only
    rw [evaluateHOLFiniteState_seq_line780,st0]; dsimp only
    rw [decl]; dsimp only
    rw [evaluateHOLFiniteState_seq_line780]
    unfold stateFreshTxPointerStore
    rw [st8]; dsimp only
    rw [stateFreshTxConstructorSequence_eq,run5,finish]
    have l2 : s2.locals = s.locals := alocals
    rw [l2]
  · rw [yglob _ (by decide),glob5 _ (by decide)]; exact ts3
  · intro name h1 h2 h3
    rw [yglob _ h3,glob5 _ h1]; change ready.globals.lookup _ = _; rw [rglob _ h1]; exact aglob name h2 h1
  · change s.clock ≤ post5.clock + 379
    have h4 : s4.clock = ready.clock := rfl
    have h2 : s2.clock = a1.clock := rfl
    rw [bc] at clk51
    rw [c64] at rclk1
    omega
  · change post5.clock ≤ s.clock
    have h4 : s4.clock = ready.clock := rfl
    have h2 : s2.clock = a1.clock := rfl
    omega

#print axioms stateFreshTx_body_memory_frame

set_option maxHeartbeats 4000000 in
/-- The original call `state_fresh_tx()`: it returns normally, keeps every word below the entry heap pointer, the
caller's locals, addresses, endianness and code; `ts` becomes the entry heap pointer, `journal_n` is reset, the heap
grows within bounds and all other globals are kept. -/
theorem stateFreshTx_call_memory_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer oldTs B oldCount : BitVec 64) (code : s.code = originalRuntimeCode)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (tsGlobal : s.globals.lookup (ofString "ts") = some (.val (.word oldTs)))
    (bsGlobal : s.globals.lookup (ofString "bs") = some (.val (.word B)))
    (counterGlobal : s.globals.lookup (ofString "journal_n") = some (.val (.word oldCount)))
    (reservation : pointer.toNat + 23024 ≤ 33806089496)
    (domain : ∀ a : BitVec 64, a.toNat < 33806089496 → s.memaddrs a)
    (ticks : 380 ≤ s.clock) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState s (.call (some (none,none)) (ofString "state_fresh_tx") []) = (none,post) ∧
      (∀ a : BitVec 64, a.toNat < pointer.toNat → post.memory a = s.memory a) ∧
      post.locals = s.locals ∧ post.memaddrs = s.memaddrs ∧ post.be = s.be ∧ post.code = s.code ∧
      (∃ P : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word P)) ∧ pointer.toNat ≤ P.toNat ∧
        P.toNat % 8 = 0 ∧ P.toNat ≤ 33806089496) ∧
      post.globals.lookup (ofString "ts") = some (.val (.word pointer)) ∧
      (∀ name, name ≠ ofString "heap_ptr" → name ≠ ofString "ts" → name ≠ ofString "journal_n" →
        post.globals.lookup name = s.globals.lookup name) ∧
      s.clock ≤ post.clock + 380 ∧ post.clock ≤ s.clock := by
  let E := callEntryStateHOLFinite s HolFiniteMapExact.empty
  obtain ⟨Y,body,mem,ma,mb,mc,hP,hts,glob,clk1,clk2⟩ := stateFreshTx_body_memory_frame E pointer oldTs B oldCount
    (by exact code) (by exact heap) (by exact tsGlobal) (by exact bsGlobal) (by exact counterGlobal) reservation
    (by exact domain) (by change 379 ≤ s.clock - 1; omega)
  have lookup := pan_no_args_lookup s.code.lookup (ofString "state_fresh_tx")
    (sourceFunctionBody Guest.guestFn_state_fresh_tx) (by rw [code]; exact originalRuntimeCode_stateFreshTx_lookup)
  have call := evaluateHOLFiniteState_call_return_caller_locals s none (ofString "state_fresh_tx") [] []
    (sourceFunctionBody Guest.guestFn_state_fresh_tx) HolFiniteMapExact.empty .one (.val (.word (0 : BitVec 64))) _
    rfl lookup (by omega) body (by simp [shapeOfHOLExact,shapeEqHOL])
  refine ⟨_,call,fun a h => mem a h,rfl,ma,mb,mc,hP,hts,glob,?_,?_⟩
  · change s.clock ≤ Y.clock + 380; change s.clock - 1 ≤ Y.clock + 379 at clk1; omega
  · change Y.clock ≤ s.clock; change Y.clock ≤ s.clock - 1 at clk2; omega

#print axioms stateFreshTx_call_memory_frame

/-- The block-level start of a transaction in `apply_body` (`state_fresh_tx(); track_ancestor_access(1);`):
both calls return normally, and every word below the entry heap pointer other than the two ancestor cells of the
block record is unchanged; `bs` is kept. -/
theorem freshTx_trackAncestor_frame {F : Type} (s m r : PanSemStateFiniteExact 64 F)
    (pointer oldTs B oldCount : BitVec 64) (code : s.code = originalRuntimeCode)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (tsGlobal : s.globals.lookup (ofString "ts") = some (.val (.word oldTs)))
    (bsGlobal : s.globals.lookup (ofString "bs") = some (.val (.word B)))
    (counterGlobal : s.globals.lookup (ofString "journal_n") = some (.val (.word oldCount)))
    (reservation : pointer.toNat + 23024 ≤ 33806089496)
    (domain : ∀ a : BitVec 64, a.toNat < 33806089496 → s.memaddrs a)
    (ticks : 380 ≤ s.clock)
    (run1 : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "state_fresh_tx") []) = (none,m))
    (run2 : evaluateHOLFiniteState m (.call (some (none,none)) (ofString "track_ancestor_access") [.const 1]) = (none,r))
    (d56 : (B + 56).toNat < 33806089496) (d64 : (B + 64).toNat < 33806089496) :
    (∀ a : BitVec 64, a.toNat < pointer.toNat → a ≠ B + 56 → a ≠ B + 64 → r.memory a = s.memory a) ∧
      r.globals.lookup (ofString "bs") = some (.val (.word B)) ∧
      r.memaddrs = s.memaddrs ∧ r.be = s.be ∧ r.code = s.code ∧ r.locals = s.locals ∧
      (∃ P : BitVec 64, r.globals.lookup (ofString "heap_ptr") = some (.val (.word P)) ∧ pointer.toNat ≤ P.toNat ∧
        P.toNat % 8 = 0 ∧ P.toNat ≤ 33806089496) := by
  obtain ⟨post,call,mem,ml,ma,mb,mc,hP,_,glob,_,_⟩ := stateFreshTx_call_memory_frame s pointer oldTs B oldCount code heap
    tsGlobal bsGlobal counterGlobal reservation domain ticks
  rw [run1] at call
  obtain ⟨_,rfl⟩ := Prod.mk.inj call
  have bs1 : m.globals.lookup (ofString "bs") = some (.val (.word B)) := by
    rw [glob _ (by decide) (by decide) (by decide)]; exact bsGlobal
  obtain ⟨rg,rl,ra,rb,rc,rmem⟩ := trackAncestor_call_normal m r (.const 1) B 1 (mc.trans code) bs1
    (by rw [evalListHOLFinite_eq_toExact]; rfl) (by rw [ma]; exact domain _ d56) (by rw [ma]; exact domain _ d64) run2
  refine ⟨fun a lt n1 n2 => by rw [rmem a n1 n2]; exact mem a lt,by rw [rg]; exact bs1,ra.trans ma,rb.trans mb,
    rc.trans mc,rl.trans ml,by rw [rg]; exact hP⟩

#print axioms freshTx_trackAncestor_frame
end InitECandidate.Runtime
