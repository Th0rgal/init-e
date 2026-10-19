import InitECandidate.Runtime.HtabGrowTop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-! `htab_union_into` contracts that also keep the destination's block below the heap pointer: the
block is the initial one, or a fresh one at or above the entry heap pointer ending at or below the
current heap pointer (`UnionCtx.TopClause`). This lets later calls' frames cover grown tables. -/

/-- The destination block is the initial one, or a fresh one at or above the entry heap pointer
that ends at or below the current heap pointer. -/
def UnionCtx.TopClause (c : UnionCtx) (lo hi : Nat) (g : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  (lo = c.lo0 ∧ hi = c.hi0) ∨ (c.pointer0.toNat ≤ lo ∧ ∃ p : BitVec 64,
    g.lookup (ofString "heap_ptr") = some (.val (.word p)) ∧ hi ≤ p.toNat)

/-- The destination table during the loop, after `I` source items. -/
def UnionCtx.DstT (c : UnionCtx) (I : BitVec 64) {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ (capacity keys used values order orderPos count : BitVec 64) (bits lo hi : Nat),
    HtabLaid c.keyLength c.dst keys c.stride capacity used values order orderPos count bits lo hi s ∧
    OrderInv s capacity count used order orderPos ∧ count.toNat < capacity.toNat ∧
    c.count0.toNat ≤ count.toNat ∧ count.toNat ≤ c.count0.toNat + I.toNat ∧
    (capacity.toNat ≤ c.capacity0.toNat ∨ capacity.toNat ≤ 4 * count.toNat) ∧
    c.TopClause lo hi s.globals

/-- Loop rank: counter I ≤ n with at most m items left, the loop locals, the source reads
unchanged, the destination table and the heap pointer. -/
def UnionRankT (c : UnionCtx) {F : Type} (s : PanSemStateFiniteExact 64 F) (m : Nat) : Prop :=
  ∃ I : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat ≤ c.n.toNat ∧
    c.n.toNat - I.toNat ≤ m ∧
    s.locals.lookup (ofString "cap") = some (.val (.word c.n)) ∧
    s.locals.lookup (ofString "dst") = some (.val (.word c.dst)) ∧
    s.locals.lookup (ofString "src") = some (.val (.word c.src)) ∧
    s.memaddrs = c.A0 ∧ (∀ w, c.Away w → s.memory w = c.M0 w) ∧ c.DstT I s ∧ c.Heap s

/-- One loop iteration from a ranked state with a remaining item is bounded by the step cost. -/
theorem union_iter_boundedT (c : UnionCtx) (ok : c.Ok) (reads : c.SrcReads) {F : Type} (s : PanSemStateFiniteExact 64 F)
    (m : Nat) (code : s.code = originalRuntimeCode) (ranked : UnionRankT c s m) (I : BitVec 64)
    (iL : s.locals.lookup (ofString "i") = some (.val (.word I))) (lt : I.toNat < c.n.toNat)
    (budget : c.stepCost ≤ s.clock) : RunBounded s unionIter c.stepCost := by
  obtain ⟨I',iL',ILe,_,_,dL,srcL,addrs,mem,⟨capacity,keys,used,values,order,orderPos,count,bits,lo,hi,laid,tables,room,
    _,cle,capB,_⟩,⟨p,heap,pLe,pAl,pIn⟩,_⟩ := ranked
  rw [iL] at iL'
  simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at iL'
  subst iL'
  have okc := ok
  obtain ⟨hdr,_,_,arena,small,_,_,_⟩ := okc
  have costLe := union_set_cost_le c ok I capacity count ILe cle capB
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "src"),.var .local (ofString "i")] = some [.val (.word c.src),.val (.word I)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,srcL,iL]
  unfold unionIter
  unfold UnionCtx.stepCost at budget ⊢
  refine RunBounded.decCall args (by omega) ?_
  intro body locals rs lookup
  rw [pan_two_word_lookup_shape s.code.lookup (ofString "htab_item") (ofString "t") (ofString "ordinal")
    (sourceFunctionBody Guest.guestFn_htab_item) (.comb [.one,.one,.one]) c.src I (by decide)
    (by rw [code]; exact vmLookup_htab_item)] at lookup
  simp only [Option.some.injEq,Prod.mk.injEq] at lookup
  obtain ⟨rfl,rfl,rfl⟩ := lookup
  refine ⟨?_,?_⟩
  · obtain ⟨ps,bd,rs',lk,pb⟩ := vmBound_htab_item
    rw [vmLookup_htab_item] at lk
    simp only [Option.some.injEq,Prod.mk.injEq] at lk
    obtain ⟨_,rfl,_⟩ := lk
    exact RunBounded.ofProg pb (by exact code) (by change 1 ≤ s.clock - 1; omega)
  · intro value post run tailBudget
    obtain ⟨b,kp,vv,rfl⟩ := union_item_returned c reads s post I lt code addrs mem _ run
    have frame := htabItem_memoryFrame (callEntryStateHOLFinite s
      ((HolFiniteMapExact.empty.update (ofString "t",.val (.word c.src))).update (ofString "ordinal",.val (.word I))))
      (by exact code)
    have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s
      ((HolFiniteMapExact.empty.update (ofString "t",.val (.word c.src))).update (ofString "ordinal",.val (.word I))))
      (sourceFunctionBody Guest.guestFn_htab_item)
    rw [run] at frame meta'
    generalize hT : setVarHOLFinite (ofString "s") (.rStruct [.val (.word b),.val (.word kp),.val (.word vv)])
      {post with locals := s.locals} = T
    have tm : T.memory = s.memory := by rw [← hT]; exact frame.1
    have tg : T.globals = s.globals := by rw [← hT]; exact frame.2
    have ta : T.memaddrs = s.memaddrs := by rw [← hT]; exact meta'.2.1
    have tb : T.be = s.be := by rw [← hT]; exact meta'.2.2.1
    have tc : T.code = s.code := by rw [← hT]; exact meta'.1
    have tk : T.clock = post.clock := by rw [← hT]; rfl
    have tS : T.locals.lookup (ofString "s") = some (.rStruct [.val (.word b),.val (.word kp),.val (.word vv)]) := by
      rw [← hT]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have tD : T.locals.lookup (ofString "dst") = some (.val (.word c.dst)) := by
      rw [← hT]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,dL]
    refine RunBounded.seq (a := setBodyCost c.keyLength (BitVec.ofNat 64 c.capMax)
      (BitVec.ofNat 64 (c.count0.toNat + c.n.toNat)) + 1) (b := 0) ?_ (by omega) ?_
    · obtain ⟨gw,guard⟩ := union_guard_word T b kp vv tS
      unfold unionSetIte
      refine RunBounded.iteWord T _ gw guard (fun _ => ?_) (fun _ => ?_)
      · refine RunBounded.weaken (runBounded_htabSet_call_laid T none _ _ _ c.keyLength c.dst keys c.stride capacity used
          values order orderPos count kp vv p bits lo hi (laid.transfer tm ta tb tc) (union_set_args T c.dst b kp vv tD tS)
          (by rw [tg]; exact heap) pAl (by omega) pIn (fun a h1 h2 h3 => by rw [ta,addrs]; exact arena a h1 h2 h3) room small
          (by omega)) (by omega)
      · exact RunBounded.weaken (RunBounded.ofProg (ProgBounded.straight _ (by decide)) (tc.trans code) (Nat.zero_le _))
          (Nat.zero_le _)
    · intro next _ nextCode _
      exact RunBounded.ofProg (ProgBounded.straight _ (by decide)) (nextCode.trans (tc.trans code)) (Nat.zero_le _)

#print axioms union_iter_boundedT

/-- A normal loop iteration advances the counter and keeps the rank invariant. -/
theorem union_iter_normalT (c : UnionCtx) (ok : c.Ok) (reads : c.SrcReads) {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (m : Nat) (code : s.code = originalRuntimeCode) (ranked : UnionRankT c s (m + 1)) (I : BitVec 64)
    (iL : s.locals.lookup (ofString "i") = some (.val (.word I))) (lt : I.toNat < c.n.toNat)
    (budget : c.stepCost ≤ s.clock)
    (run : evaluateHOLFiniteState s unionIter = (none,post)) :
    UnionRankT c post m ∧ post.code = s.code := by
  obtain ⟨I',iL',ILe,left,capL,dL,srcL,addrs,mem,⟨capacity,keys,used,values,order,orderPos,count,bits,lo,hi,laid,tables,room,
    c0le,cle,capB,loB⟩,⟨p,heap,pLe,pAl,pIn⟩,rel⟩ := ranked
  rw [iL] at iL'
  simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at iL'
  subst iL'
  have okc := ok
  obtain ⟨hdr,_,_,arena,small,cap0,n0,c0⟩ := okc
  have costLe := union_set_cost_le c ok I capacity count ILe cle capB
  have noWrap : (I + 1).toNat = I.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by change I.toNat + 1 < 2 ^ 64; omega)]; rfl
  unfold unionIter at run
  obtain ⟨vals,body,callee,rs,w,bodyPost,resumed,inner,args',lookup',bodyRun,rm,ra,rb,rc,rg,rclk,rname,rothers,contRun,
    pm,pa,pb,pc,pg,plocals⟩ := decCall_normal_globals run
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "src"),.var .local (ofString "i")] = some [.val (.word c.src),.val (.word I)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,srcL,iL]
  rw [args] at args'
  simp only [Option.some.injEq] at args'
  subst args'
  rw [pan_two_word_lookup_shape s.code.lookup (ofString "htab_item") (ofString "t") (ofString "ordinal")
    (sourceFunctionBody Guest.guestFn_htab_item) (.comb [.one,.one,.one]) c.src I (by decide)
    (by rw [code]; exact vmLookup_htab_item)] at lookup'
  simp only [Option.some.injEq,Prod.mk.injEq] at lookup'
  obtain ⟨rfl,rfl,rfl⟩ := lookup'
  obtain ⟨b,kp,vv,rfl⟩ := union_item_returned c reads s bodyPost I lt code addrs mem _ bodyRun
  have frame := htabItem_memoryFrame (callEntryStateHOLFinite s
    ((HolFiniteMapExact.empty.update (ofString "t",.val (.word c.src))).update (ofString "ordinal",.val (.word I))))
    (by exact code)
  have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s
    ((HolFiniteMapExact.empty.update (ofString "t",.val (.word c.src))).update (ofString "ordinal",.val (.word I))))
    (sourceFunctionBody Guest.guestFn_htab_item)
  rw [bodyRun] at frame meta'
  have resClock : s.clock - 2 ≤ resumed.clock := by
    obtain ⟨ps,bd,rs',lk,pb⟩ := vmBound_htab_item
    rw [vmLookup_htab_item] at lk
    simp only [Option.some.injEq,Prod.mk.injEq] at lk
    obtain ⟨_,rfl,_⟩ := lk
    have h := pb (callEntryStateHOLFinite s
      ((HolFiniteMapExact.empty.update (ofString "t",.val (.word c.src))).update (ofString "ordinal",.val (.word I))))
      (by exact code) (by change 1 ≤ s.clock - 1; unfold UnionCtx.stepCost at budget; omega)
    rw [bodyRun] at h
    obtain ⟨h1,h2,_⟩ := h
    change s.clock - 1 ≤ bodyPost.clock + 1 at h1
    rw [rclk h2]
    omega
  have qm : resumed.memory = s.memory := rm.trans frame.1
  have qg : resumed.globals = s.globals := rg.trans frame.2
  have qa : resumed.memaddrs = s.memaddrs := ra.trans meta'.2.1
  have qb : resumed.be = s.be := rb.trans meta'.2.2.1
  have qc : resumed.code = s.code := rc.trans meta'.1
  have qD : resumed.locals.lookup (ofString "dst") = some (.val (.word c.dst)) := (rothers _ (by decide)).trans dL
  have qI : resumed.locals.lookup (ofString "i") = some (.val (.word I)) := (rothers _ (by decide)).trans iL
  rw [evaluateHOLFiniteState_seq_line780] at contRun
  cases iteRun : evaluateHOLFiniteState resumed unionSetIte with
  | mk ir mid =>
    rw [iteRun] at contRun
    cases ir with
    | some r => simp at contRun
    | none =>
      simp only at contRun
      have key : mid.locals = resumed.locals ∧ mid.memaddrs = c.A0 ∧ mid.code = s.code ∧
          (∀ w, c.Away w → mid.memory w = c.M0 w) ∧ c.DstT (I + 1) mid ∧ c.Heap mid := by
        unfold unionSetIte at iteRun
        rcases ite_normal_cases_cond resumed mid _ _ _ iteRun with ⟨gw,_,_,setRun⟩ | ⟨_,skipRun⟩
        · obtain ⟨⟨c',k',u',v',o',op',n',b',lo',hi',laid',tables',counts,capB',loB'⟩,mlocals,maddrs,mbe,mframe⟩ :=
            htabSet_call_normal_laidTop resumed mid _ _ _ c.keyLength c.dst keys c.stride capacity used values order orderPos
              count kp vv p bits lo hi (laid.transfer qm qa qb qc) (union_set_args resumed c.dst b kp vv qD rname)
              (by rw [qg]; exact heap) pAl (by omega) pIn (fun a h1 h2 h3 => by rw [qa,addrs]; exact arena a h1 h2 h3)
              (tables.transfer qm qa qb) room small (by unfold UnionCtx.stepCost at budget; omega) setRun
          have setRel : HeapRel resumed.globals mid.globals := by
            have := normalRel_apply (htabSet_call_normalRel
              [.var .local (ofString "dst"),.rfield 1 (.var .local (ofString "s")),.rfield 2 (.var .local (ofString "s"))])
              (X := resumed) (by rw [setRun]; exact Or.inl rfl) (qc.trans code)
            rw [setRun] at this
            exact this
          rw [qg] at setRel
          have midMeta := evaluateHOLFiniteState_metadata resumed (.call (some (none,none)) (ofString "htab_set")
            [.var .local (ofString "dst"),.rfield 1 (.var .local (ofString "s")),.rfield 2 (.var .local (ofString "s"))])
          rw [setRun] at midMeta
          obtain ⟨p1,heap1,pp1,a1,i1⟩ := setRel.2 p heap pAl pIn
          refine ⟨mlocals,maddrs.trans (qa.trans addrs),midMeta.1.trans qc,fun w away => ?_,?_,
            ⟨⟨p1,heap1,by omega,a1,i1⟩,heapRel_preorder.trans _ _ _ rel setRel⟩⟩
          · obtain ⟨wp,wh,wl⟩ := away
            rw [mframe w (by omega) wh (by rcases loB with ⟨rfl,rfl⟩ | ⟨lp,_,_,_⟩ <;> omega),qm]
            exact mem w ⟨wp,wh,wl⟩
          · refine ⟨c',k',u',v',o',op',n',b',lo',hi',laid',tables',?_,?_,?_,?_,?_⟩
            · rcases counts with ⟨rfl,rfl⟩ | ⟨e1,e2⟩ <;> omega
            · rcases counts with ⟨rfl,rfl⟩ | ⟨e1,e2⟩ <;> omega
            · rw [noWrap]; rcases counts with ⟨rfl,rfl⟩ | ⟨e1,e2⟩ <;> omega
            · rcases capB' with rfl | lt4
              · rcases counts with ⟨_,rfl⟩ | ⟨e1,e2⟩ <;> omega
              · omega
            · rcases loB' with ⟨rfl,rfl⟩ | ⟨lp,pT,hpT,leT⟩
              · rcases loB with lb | ⟨lb,pq,hpq,leq⟩
                · exact Or.inl lb
                · rw [heap] at hpq
                  simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at hpq
                  subst hpq
                  exact Or.inr ⟨lb,p1,heap1,by omega⟩
              · exact Or.inr ⟨by omega,pT,hpT,leT⟩
        · rw [evaluateHOLFiniteState_skip] at skipRun
          obtain ⟨_,rfl⟩ := Prod.mk.inj skipRun
          refine ⟨rfl,qa.trans addrs,qc,fun w away => by rw [qm]; exact mem w away,
            ⟨capacity,keys,used,values,order,orderPos,count,bits,lo,hi,laid.transfer qm qa qb qc,tables.transfer qm qa qb,
              room,c0le,by rw [noWrap]; omega,capB,by rw [qg]; exact loB⟩,⟨⟨p,by rw [qg]; exact heap,pLe,pAl,pIn⟩,by rw [qg]; exact rel⟩⟩
      obtain ⟨mlocals,maddrs,mcode,mmem,⟨c',k',u',v',o',op',n',b',lo',hi',laid',tables',r1,r2,r3,r4,r5⟩,
        ⟨p1,heap1,pp1,a1,i1⟩,rel1⟩ := key
      have mI : mid.locals.lookup (ofString "i") = some (.val (.word I)) := by rw [mlocals]; exact qI
      unfold unionIncr at contRun
      rw [evaluate_increment_local mid (ofString "i") I mI] at contRun
      obtain ⟨_,rfl⟩ := Prod.mk.inj contRun
      have keep : ∀ x, x ≠ ofString "s" → x ≠ ofString "i" → post.locals.lookup x = s.locals.lookup x := by
        intro x ns ni
        rw [plocals x ns]
        simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ni]
        rw [mlocals]
        exact rothers x ns
      refine ⟨⟨I + 1,?_,by rw [noWrap]; omega,by rw [noWrap]; omega,
        by rw [keep _ (by decide) (by decide)]; exact capL,
        by rw [keep _ (by decide) (by decide)]; exact dL,
        by rw [keep _ (by decide) (by decide)]; exact srcL,
        pa.trans maddrs,fun w away => by rw [pm]; exact mmem w away,
        ⟨c',k',u',v',o',op',n',b',lo',hi',laid'.transfer pm pa pb pc,tables'.transfer pm pa pb,r1,r2,r3,r4,by rw [pg]; exact r5⟩,
        ⟨⟨p1,by rw [pg]; exact heap1,pp1,a1,i1⟩,by rw [pg]; exact rel1⟩⟩,pc.trans mcode⟩
      rw [plocals _ (by decide)]
      simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms union_iter_normalT

theorem UnionRankT.transfer (c : UnionCtx) {F : Type} {s r : PanSemStateFiniteExact 64 F} {m : Nat}
    (ranked : UnionRankT c s m) (memory : r.memory = s.memory) (memaddrs : r.memaddrs = s.memaddrs) (be : r.be = s.be)
    (code : r.code = s.code) (globals : r.globals = s.globals) (locals : r.locals = s.locals) : UnionRankT c r m := by
  obtain ⟨I,iL,a1,a2,capL,dL,srcL,addrs,mem,⟨capacity,keys,used,values,order,orderPos,count,bits,lo,hi,laid,tables,r1,r2,r3,r4,r5⟩,
    ⟨⟨p,heap,h1,h2,h3⟩,rel⟩⟩ := ranked
  exact ⟨I,by rw [locals]; exact iL,a1,a2,by rw [locals]; exact capL,by rw [locals]; exact dL,by rw [locals]; exact srcL,
    memaddrs.trans addrs,fun w away => by rw [memory]; exact mem w away,
    ⟨capacity,keys,used,values,order,orderPos,count,bits,lo,hi,laid.transfer memory memaddrs be code,
      tables.transfer memory memaddrs be,r1,r2,r3,r4,by rw [globals]; exact r5⟩,⟨⟨p,by rw [globals]; exact heap,h1,h2,h3⟩,by rw [globals]; exact rel⟩⟩

/-- The union loop from rank m runs within m * (stepCost + 1) ticks, and a normal exit keeps the rank. -/
theorem unionLoop_runT (c : UnionCtx) (ok : c.Ok) (reads : c.SrcReads) :
    ∀ m : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
      UnionRankT c state m → m * (c.stepCost + 1) ≤ state.clock →
      RankedOutcome state unionCond (m * (c.stepCost + 1)) (UnionRankT c) False
        (evaluateHOLFiniteState state (.while unionCond unionIter)) := by
  have nSmall : c.n.toNat < 2 ^ 63 := by obtain ⟨_,_,_,_,_,_,n0,_⟩ := ok; omega
  refine rankedWhile_run _ unionIter c.stepCost (UnionRankT c) False ?_ ?_
  · intro F s ranked v hv
    obtain ⟨I,iL,ILe,left,capL,_⟩ := ranked
    unfold unionCond at hv
    rw [eval_localBound_less s (ofString "i") (ofString "cap") .less (Or.inl rfl) I c.n (by omega) nSmall iL capL] at hv
    have : ¬ I.toNat < c.n.toNat := by omega
    simp [this] at hv
    exact hv.symm
  · intro F s m v code' ranked hv nonzero budget'
    have rankedD : UnionRankT c (decClockHOLFinite s) (m + 1) := ranked.transfer c rfl rfl rfl rfl rfl rfl
    obtain ⟨I,iL,ILe,left,capL,_⟩ := ranked
    unfold unionCond at hv
    rw [eval_localBound_less s (ofString "i") (ofString "cap") .less (Or.inl rfl) I c.n (by omega) nSmall iL capL] at hv
    have lt : I.toNat < c.n.toNat := by
      by_cases h : I.toNat < c.n.toNat
      · exact h
      · simp [h] at hv; exact absurd hv.symm nonzero
    have bounded := union_iter_boundedT c ok reads (decClockHOLFinite s) (m + 1) code' rankedD I iL lt
      (by change _ ≤ s.clock - 1; omega)
    obtain ⟨b1,b2,b3⟩ := bounded
    refine ⟨b1,b2,b3,?_,?_⟩
    · intro flow
      rcases flow with normal | cont
      · cases hrun : evaluateHOLFiniteState (decClockHOLFinite s) unionIter with
        | mk r post =>
          rw [hrun] at normal
          simp only at normal
          subst normal
          obtain ⟨rk,pc⟩ := union_iter_normalT c ok reads (decClockHOLFinite s) post m code' rankedD I iL lt
            (by change _ ≤ s.clock - 1; omega) hrun
          exact ⟨m,le_refl _,rk,pc⟩
      · exact absurd cont (evaluate_noTopContinue unionIter (by decide) (decClockHOLFinite s))
    · intro brk
      exact absurd brk (evaluate_noTopBreak unionIter (by decide) (decClockHOLFinite s))

#print axioms unionLoop_runT

/-- The original `htab_union_into` body, from a destination table of either actual layout and a
source whose read words are mapped, word-valued and away from the destination footprint: it returns
0 with a destination table of either layout at count ≤ count0 + n, the heap pointer only grown, and
every word below the entry heap pointer outside the destination header and initial block unchanged. -/
theorem htabUnionInto_returnedT (c : UnionCtx) (ok : c.Ok) (reads : c.SrcReads) {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) (code : state.code = originalRuntimeCode)
    (dstL : state.locals.lookup (ofString "dst") = some (.val (.word c.dst)))
    (srcL : state.locals.lookup (ofString "src") = some (.val (.word c.src)))
    (nDomain : state.memaddrs (c.src + 24)) (nCell : state.memory (c.src + 24) = .word c.n)
    (memory0 : c.M0 = state.memory) (memaddrs0 : c.A0 = state.memaddrs) (globals0 : c.G0 = state.globals)
    (dst0 : ∃ (keys used values order orderPos : BitVec 64) (bits : Nat),
      HtabLaid c.keyLength c.dst keys c.stride c.capacity0 used values order orderPos c.count0 bits c.lo0 c.hi0 state ∧
      OrderInv state c.capacity0 c.count0 used order orderPos)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word c.pointer0)))
    (budget : c.n.toNat * (c.stepCost + 1) ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_union_into) = (some (.returned v),post)) :
    v = .val (.word 0) ∧ c.DstT c.n post ∧ c.Heap post ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ post.code = state.code ∧
      ∀ w, c.Away w → post.memory w = state.memory w := by
  have okc := ok
  obtain ⟨_,pAl,pIn,_,_,_,_,c0⟩ := okc
  rw [source_htabUnionInto_body] at run
  obtain ⟨cv,s1r,e1,run1,m1,a1,b1,k1,g1⟩ := dec_returned_globals run
  rw [eval_load_word state _ (c.src + 24) c.n (eval_add2 state _ _ c.src 24 (item_eval_locals state _ _ srcL)
    (item_eval_const state 24)) nDomain nCell] at e1
  cases e1
  obtain ⟨iv,s2r,e2,run2,m2,a2,b2,k2,g2⟩ := dec_returned_globals run1
  rw [item_eval_const] at e2
  cases e2
  generalize hs2 : setVarHOLFinite (ofString "i") (.val (.word 0))
    (setVarHOLFinite (ofString "cap") (.val (.word c.n)) state) = s2 at run2
  have rank0 : UnionRankT c s2 c.n.toNat := by
    obtain ⟨keys,used,values,order,orderPos,bits,laid,tables⟩ := dst0
    rw [← hs2]
    refine ⟨0,by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],by simp,by simp,
      by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],
      by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,dstL],
      by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,srcL],
      memaddrs0.symm,fun w _ => by rw [memory0]; rfl,
      ⟨c.capacity0,keys,used,values,order,orderPos,c.count0,bits,c.lo0,c.hi0,laid.transfer rfl rfl rfl rfl,
        tables.transfer rfl rfl rfl,c0,le_refl _,by simp,Or.inl (le_refl _),Or.inl ⟨rfl,rfl⟩⟩,
      ⟨⟨c.pointer0,heap,le_refl _,pAl,pIn⟩,by rw [globals0]; exact heapRel_preorder.refl _⟩⟩
  have s2code : s2.code = originalRuntimeCode := by rw [← hs2]; exact code
  have s2clock : s2.clock = state.clock := by rw [← hs2]; rfl
  have s2meta : s2.memory = state.memory ∧ s2.memaddrs = state.memaddrs ∧ s2.be = state.be ∧ s2.globals = state.globals := by
    rw [← hs2]; exact ⟨rfl,rfl,rfl,rfl⟩
  rw [evaluateHOLFiniteState_seq_line780] at run2
  cases loopRun : evaluateHOLFiniteState s2 (.while unionCond unionIter) with
  | mk lr ls =>
    have outcome := unionLoop_runT c ok reads c.n.toNat s2 s2code rank0 (by rw [s2clock]; exact budget)
    have loopShape : (.while unionCond unionIter : ProgHOL 64) =
        .while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "cap")))
          (.decCall (ofString "s") (.comb [.one,.one,.one]) (ofString "htab_item")
            [.var .local (ofString "src"),.var .local (ofString "i")]
            (.seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s"))) (.const 0))
                (.call (some (none,none)) (ofString "htab_set")
                  [.var .local (ofString "dst"),.rfield 1 (.var .local (ofString "s")),.rfield 2 (.var .local (ofString "s"))])
                .skip)
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])))) := rfl
    rw [← loopShape,loopRun] at run2
    rw [loopRun] at outcome
    cases lr with
    | some r =>
      exfalso
      obtain ⟨e,_⟩ := Prod.mk.inj run2
      simp only [Option.some.injEq] at e
      subst e
      exact unionLoop_not_returned s2 ls v loopRun
    | none =>
      simp only at run2
      obtain ⟨_,_,_,normal⟩ := outcome
      obtain ⟨m,rk,lcode,_⟩ := normal rfl
      obtain ⟨ve,rm,ra,rb,rc,rg⟩ := return_const_globals ls s2r 0 v run2
      obtain ⟨I,_,ILe,_,_,_,_,laddrs,lmem,⟨capacity,keys,used,values,order,orderPos,count,bits,lo,hi,laid,tables,r1,r2,r3,r4,r5⟩,
        heapL⟩ := rk
      have pPost : post.memory = ls.memory ∧ post.memaddrs = ls.memaddrs ∧ post.be = ls.be ∧ post.code = ls.code ∧
          post.globals = ls.globals :=
        ⟨m1.trans (m2.trans rm),a1.trans (a2.trans ra),b1.trans (b2.trans rb),k1.trans (k2.trans rc),g1.trans (g2.trans rg)⟩
      have lmeta := evaluateHOLFiniteState_metadata s2 (.while unionCond unionIter)
      rw [loopRun] at lmeta
      refine ⟨ve,⟨capacity,keys,used,values,order,orderPos,count,bits,lo,hi,
          laid.transfer pPost.1 pPost.2.1 pPost.2.2.1 pPost.2.2.2.1,tables.transfer pPost.1 pPost.2.1 pPost.2.2.1,
          r1,r2,by omega,r4,by rw [pPost.2.2.2.2]; exact r5⟩,?_,pPost.2.1.trans (lmeta.2.1.trans s2meta.2.1),
        pPost.2.2.1.trans (lmeta.2.2.1.trans s2meta.2.2.1),pPost.2.2.2.1.trans (lcode.trans (s2code.trans code.symm)),
        fun w away => by rw [pPost.1,lmem w away,memory0]⟩
      obtain ⟨⟨p,hp,h1,h2,h3⟩,rel⟩ := heapL
      exact ⟨⟨p,by rw [pPost.2.2.2.2]; exact hp,h1,h2,h3⟩,by rw [pPost.2.2.2.2]; exact rel⟩

#print axioms htabUnionInto_returnedT

/-- The discarded `htab_union_into(dst, src)` call with the contract of `htabUnionInto_returnedT`. -/
theorem htabUnionInto_call_normalT (c : UnionCtx) (ok : c.Ok) (reads : c.SrcReads) {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (dstArgument srcArgument : ExpHOL 64)
    (code : state.code = originalRuntimeCode)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [dstArgument,srcArgument] =
      some [.val (.word c.dst),.val (.word c.src)])
    (nDomain : state.memaddrs (c.src + 24)) (nCell : state.memory (c.src + 24) = .word c.n)
    (memory0 : c.M0 = state.memory) (memaddrs0 : c.A0 = state.memaddrs) (globals0 : c.G0 = state.globals)
    (dst0 : ∃ (keys used values order orderPos : BitVec 64) (bits : Nat),
      HtabLaid c.keyLength c.dst keys c.stride c.capacity0 used values order orderPos c.count0 bits c.lo0 c.hi0 state ∧
      OrderInv state c.capacity0 c.count0 used order orderPos)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word c.pointer0)))
    (budget : c.n.toNat * (c.stepCost + 1) + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_union_into") [dstArgument,srcArgument]) =
      (none,post)) :
    c.DstT c.n post ∧ c.Heap post ∧ post.locals = state.locals ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ post.code = state.code ∧
      ∀ w, c.Away w → post.memory w = state.memory w := by
  obtain ⟨v,output,bodyRun,pm,pl,pg,pa,pb,pc⟩ := evaluate_discard_normal_body_globals state post _ _ _ _ _ _ args
    (htabUnionInto_installed state c.dst c.src code) run
  obtain ⟨_,dst,heapO,oa,ob,oc,frame⟩ := htabUnionInto_returnedT c ok reads (callEntryStateHOLFinite state
      ((HolFiniteMapExact.empty.update (ofString "dst",.val (.word c.dst))).update (ofString "src",.val (.word c.src)))) output v (by exact code)
    (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by exact nDomain) (by exact nCell) (by exact memory0) (by exact memaddrs0) (by exact globals0)
    (by
      obtain ⟨keys,used,values,order,orderPos,bits,laid,tables⟩ := dst0
      exact ⟨keys,used,values,order,orderPos,bits,laid.transfer rfl rfl rfl rfl,tables.transfer rfl rfl rfl⟩)
    (by exact heap) (by change _ ≤ state.clock - 1; omega) bodyRun
  obtain ⟨capacity,keys,used,values,order,orderPos,count,bits,lo,hi,laid,tables,r1,r2,r3,r4,r5⟩ := dst
  obtain ⟨⟨p,hp,h1,h2,h3⟩,rel⟩ := heapO
  exact ⟨⟨capacity,keys,used,values,order,orderPos,count,bits,lo,hi,laid.transfer pm pa pb pc,tables.transfer pm pa pb,
      r1,r2,r3,r4,by rw [pg]; exact r5⟩,⟨⟨p,by rw [pg]; exact hp,h1,h2,h3⟩,by rw [pg]; exact rel⟩,pl,pa.trans oa,pb.trans ob,pc.trans oc,
    fun w away => by rw [pm]; exact frame w away⟩

#print axioms htabUnionInto_call_normalT

set_option maxHeartbeats 1000000 in
/-- The `htab_union_into(dst, src)` call costs at most n * (stepCost + 1) + 1 ticks in every outcome. -/
theorem runBounded_htabUnionInto_callT (c : UnionCtx) (ok : c.Ok) (reads : c.SrcReads) {F : Type}
    (state : PanSemStateFiniteExact 64 F) (destination : Option (VarKind × MlS)) (dstArgument srcArgument : ExpHOL 64)
    (code : state.code = originalRuntimeCode)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [dstArgument,srcArgument] =
      some [.val (.word c.dst),.val (.word c.src)])
    (nDomain : state.memaddrs (c.src + 24)) (nCell : state.memory (c.src + 24) = .word c.n)
    (memory0 : c.M0 = state.memory) (memaddrs0 : c.A0 = state.memaddrs) (globals0 : c.G0 = state.globals)
    (dst0 : ∃ (keys used values order orderPos : BitVec 64) (bits : Nat),
      HtabLaid c.keyLength c.dst keys c.stride c.capacity0 used values order orderPos c.count0 bits c.lo0 c.hi0 state ∧
      OrderInv state c.capacity0 c.count0 used order orderPos)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word c.pointer0)))
    (budget : c.n.toNat * (c.stepCost + 1) + 1 ≤ state.clock) :
    RunBounded state (.call (some (destination,none)) (ofString "htab_union_into") [dstArgument,srcArgument])
      (c.n.toNat * (c.stepCost + 1) + 1) := by
  have okc := ok
  obtain ⟨_,pAl,pIn,_,_,_,_,c0⟩ := okc
  refine RunBounded.call args budget ?_
  intro body locals returnShape lookup
  rw [htabUnionInto_installed state c.dst c.src code] at lookup
  simp only [Option.some.injEq,Prod.mk.injEq] at lookup
  obtain ⟨rfl,rfl,rfl⟩ := lookup
  generalize hE : callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "dst",.val (.word c.dst))).update (ofString "src",.val (.word c.src))) = E
  have eD : E.locals.lookup (ofString "dst") = some (.val (.word c.dst)) := by
    rw [← hE]; simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have eS : E.locals.lookup (ofString "src") = some (.val (.word c.src)) := by
    rw [← hE]; simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have eM : E.memory = state.memory ∧ E.memaddrs = state.memaddrs ∧ E.be = state.be ∧ E.code = state.code ∧
      E.globals = state.globals ∧ E.clock = state.clock - 1 := by rw [← hE]; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  rw [source_htabUnionInto_body]
  refine RunBounded.decWord E _ _ c.n (eval_load_word E _ (c.src + 24) c.n
    (eval_add2 E _ _ c.src 24 (item_eval_locals E _ _ eS) (item_eval_const E 24))
    (by rw [eM.2.1]; exact nDomain) (by rw [eM.1]; exact nCell)) ?_
  refine RunBounded.decConst _ _ _ ?_
  generalize hs2 : setVarHOLFinite (ofString "i") (.val (.word 0))
    (setVarHOLFinite (ofString "cap") (.val (.word c.n)) E) = s2
  have rank0 : UnionRankT c s2 c.n.toNat := by
    obtain ⟨keys,used,values,order,orderPos,bits,laid,tables⟩ := dst0
    rw [← hs2]
    refine ⟨0,by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],by simp,by simp,
      by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],
      by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,eD],
      by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,eS],
      by rw [memaddrs0]; exact eM.2.1,fun w _ => by rw [memory0]; exact congrFun eM.1 w,
      ⟨c.capacity0,keys,used,values,order,orderPos,c.count0,bits,c.lo0,c.hi0,
        laid.transfer eM.1 eM.2.1 eM.2.2.1 eM.2.2.2.1,tables.transfer eM.1 eM.2.1 eM.2.2.1,c0,le_refl _,by simp,
        Or.inl (le_refl _),Or.inl ⟨rfl,rfl⟩⟩,
      ⟨⟨c.pointer0,by change E.globals.lookup _ = _; rw [eM.2.2.2.2.1]; exact heap,le_refl _,pAl,pIn⟩,
        by change HeapRel c.G0 E.globals; rw [eM.2.2.2.2.1,globals0]; exact heapRel_preorder.refl _⟩⟩
  have s2code : s2.code = originalRuntimeCode := by rw [← hs2]; change E.code = _; rw [eM.2.2.2.1]; exact code
  have s2clock : s2.clock = state.clock - 1 := by rw [← hs2]; exact eM.2.2.2.2.2
  have whole : RunBounded s2 (.seq (.while unionCond unionIter) (.return (.const 0)))
      (c.n.toNat * (c.stepCost + 1) + 0) := by
    refine RunBounded.seq ?_ (by rw [s2clock]; omega) ?_
    · obtain ⟨o1,o2,o3,_⟩ := unionLoop_runT c ok reads c.n.toNat s2 s2code rank0 (by rw [s2clock]; omega)
      exact ⟨o1,o2,o3⟩
    · intro next _ nextCode _
      exact RunBounded.ofProg (ProgBounded.straight _ (by decide)) (nextCode.trans s2code) (Nat.zero_le _)
  rw [Nat.add_zero,unionLoop_shape] at whole
  exact whole

#print axioms runBounded_htabUnionInto_callT
end InitECandidate.Runtime
