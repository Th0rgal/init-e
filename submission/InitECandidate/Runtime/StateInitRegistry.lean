import InitECandidate.Runtime.HtabBlockInit
import InitECandidate.Runtime.BlockRegistryBridge
import InitECandidate.Runtime.StateInitJournalTransaction
/-!
First-transaction registry establishment over the actual original source. `block_segment_run_le`: the existing
`block_segment_run` (same proof) with the exit heap bounded by the constructor budgets. `source_stateInit_skbuf`: the
initializer after the block segment is `sk_buf = alloc(64)` followed by the journal tail. `stateInit_freshTx_regT9`:
from the state at the original `state_init` block segment, the remainder of `state_init` returns, and the original
`state_fresh_tx` from the initialized state (the same convention as `evaluate_stateInit_journal_then_transaction`)
returns into the transaction world with the nine-table registry `RegT 9` (eight transaction tables and the block
pre-state read table at `bs + 72`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

set_option maxHeartbeats 4000000 in
/-- The block-state construction inside `state_init` (`bs = alloc(80)` through the last `htab_new`): the record
is the entry heap pointer, its `ws` cell and the two ancestor cells are set, and the seven block tables are built
at their record cells in constructor order above the record, all below the exit heap pointer. Words below the
entry heap pointer are kept; globals other than `bs` and `heap_ptr` are kept. -/
theorem block_segment_run_le {F : Type} (s : PanSemStateFiniteExact 64 F) (tail : ProgHOL 64) (p0 oldB W oldT : BitVec 64)
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
      P2.toNat ≤ (allocationEnd p0 80).toNat + stateFreshTxAllocationBudget blockTablesFirst +
        stateFreshTxAllocationBudget blockTablesLast ∧
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
  refine ⟨post,P1,P2,?_,?_,?_,?_,?_,?_,built2,hP2,alP2,inP2,by rw [b1,b2]; rw [b2] at upP2; omega,cov.1,?_,?_,
    pc2.trans (pc1.trans acode),
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

#print axioms block_segment_run_le
theorem source_stateInit_skbuf :
    stateInitSpineDrop 26 (sourceFunctionBody Guest.guestFn_state_init) =
      .seq (.call (some (some (.global,ofString "sk_buf"),none)) (ofString "alloc") [.const 64]) stateInitJournalTail := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_stateInit_skbuf

/-- A natural-number room bound as the allocator's word request guard. -/
theorem alloc_request_of_room (pointer size : BitVec 64) (room : pointer.toNat + size.toNat ≤ 33806089496) :
    size ≤ (33806089496 : BitVec 64) - pointer := by
  have pointerLe : pointer ≤ (33806089496 : BitVec 64) := BitVec.le_def.mpr (by change pointer.toNat ≤ 33806089496; omega)
  apply BitVec.le_def.mpr
  rw [BitVec.toNat_sub_of_le pointerLe]
  change size.toNat ≤ 33806089496 - pointer.toNat
  omega

set_option maxHeartbeats 16000000 in
/-- First-transaction registry establishment over the actual original source: from the state at the original
`state_init` block segment, the remainder of `state_init` (block tables, `sk_buf` allocation, journal setup, return)
returns, and the original `state_fresh_tx` from the initialized state returns into the transaction world with the
nine-table content-carrying registry (eight transaction tables and the block pre-state read table at `bs + 72`) at its
exit heap. -/
theorem stateInit_freshTx_regT9 {F : Type} (s : PanSemStateFiniteExact 64 F) (p0 oldB W oldT oldSk oldCap oldJ oldCount
      oldTs snapshot : BitVec 64)
    (code : s.code = originalRuntimeCode)
    (hB : s.globals.lookup (ofString "bs") = some (.val (.word oldB)))
    (hW : s.globals.lookup (ofString "ws") = some (.val (.word W)))
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p0))) (al : p0.toNat % 8 = 0)
    (domain : ∀ a : BitVec 64, a.toNat < 33806089496 → s.memaddrs a)
    (tL : s.locals.lookup (ofString "t") = some (.val (.word oldT)))
    (hSk : s.globals.lookup (ofString "sk_buf") = some (.val (.word oldSk)))
    (hCap : s.globals.lookup (ofString "journal_cap") = some (.val (.word oldCap)))
    (hJ : s.globals.lookup (ofString "journal") = some (.val (.word oldJ)))
    (hN : s.globals.lookup (ofString "journal_n") = some (.val (.word oldCount)))
    (hTs : s.globals.lookup (ofString "ts") = some (.val (.word oldTs)))
    (space : p0.toNat + 88 + stateFreshTxAllocationBudget blockTablesFirst + stateFreshTxAllocationBudget blockTablesLast +
      72 + 16777216 + 8 + 23024 ≤ 33806089496)
    (ticks : 1 + blockClock blockTablesFirst + blockClock blockTablesLast + 382 ≤ s.clock) :
    ∃ (initialized : PanSemStateFiniteExact 64 F) (J P T72 : BitVec 64) (widths : BitVec 64 → BitVec 64)
      (post : PanSemStateFiniteExact 64 F) (H : BitVec 64),
      evaluateHOLFiniteState s (stateInitSpineDrop 8 (sourceFunctionBody Guest.guestFn_state_init)) =
        (some (.returned (.val (.word (0 : BitVec 64)))),initialized) ∧
      initialized.memory (p0 + BitVec.ofNat 64 72) = .word T72 ∧
      evaluateHOLFiniteState initialized (.call (some (none,none)) (ofString "state_fresh_tx") []) = (none,post) ∧
      TransactionRuntimeWorld widths (allocationEnd P 72) P J snapshot 0 post ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word H)) ∧ P.toNat ≤ H.toNat ∧
      (∀ ko : Fin 9, RegT 9 (c9 P (allocationEnd P 72) (p0 + BitVec.ofNat 64 72)) (T9 (allocationEnd P 72) T72)
        (fun x => x.toNat < P.toNat ∧ ¬ rollbackTableFootprint widths T72 post x) H post.memory post.memaddrs
        post.be ko) := by
  have bF : stateFreshTxAllocationBudget blockTablesFirst = 81 * 960 + 6 * 114 := by decide
  have bL : stateFreshTxAllocationBudget blockTablesLast = 81 * 256 + 114 := by decide
  have cF : blockClock blockTablesFirst = 960 + 6 * 14 := by decide
  have cL : blockClock blockTablesLast = 256 + 14 := by decide
  rw [bF,bL] at space; rw [cF,cL] at ticks
  rw [source_stateInit_block]
  obtain ⟨post1,P1,P2,run1,bs1,_,_,_,built1,built2,hP2,alP2,inP2,upP2,cov80,frame1,glob1,pc1,pa1,pb1,clk11,clk12⟩ :=
    block_segment_run_le s (stateInitSpineDrop 26 (sourceFunctionBody Guest.guestFn_state_init)) p0 oldB W oldT code hB hW
      heap al domain (by rw [bF,bL]; omega) (by rw [cF,cL]; omega) tL
  rw [bF,bL] at upP2; rw [cF,cL] at clk11
  have e80 := allocationEnd_covers p0 80 (by change p0.toNat + 80 ≤ _; omega)
  change p0.toNat + 80 ≤ _ ∧ _ < p0.toNat + 80 + 8 ∧ _ at e80
  have lo1 := BlockBuilt.le _ _ _ _ built1
  rw [run1,source_stateInit_skbuf]
  -- sk_buf = alloc(64)
  have skG : post1.globals.lookup (ofString "sk_buf") = some (.val (.word oldSk)) :=
    (glob1 _ (by decide) (by decide)).trans hSk
  have e64 : (64 : BitVec 64).toNat = 64 := rfl
  obtain ⟨r1,skRun,rclk,rmem,_,rcode,raddr,rbe,_,rheap,rglob⟩ := evaluate_alloc_global_call post1 (.const 64) P2 64 oldSk
    (ofString "sk_buf") (by rw [evalListHOLFinite_eq_toExact]; rfl) (pc1.trans code) (by omega) hP2 skG (by decide)
    (alloc_request_of_room P2 64 (by rw [e64]; omega))
    (allocationEnd_within_heap P2 64 (by omega) (alloc_request_of_room P2 64 (by rw [e64]; omega)))
  have c64 := allocationEnd_covers P2 64 (by rw [e64]; omega)
  rw [e64] at c64
  set P3 := allocationEnd P2 64 with hP3
  rw [evaluateHOLFiniteState_seq_line780,skRun]
  dsimp only
  -- journal setup and return
  have g1 : ∀ name, name ≠ ofString "sk_buf" → name ≠ ofString "heap_ptr" → name ≠ ofString "bs" →
      r1.globals.lookup name = s.globals.lookup name := fun name a b c =>
    (rglob name a b).trans (glob1 name b c)
  have e16 : (16777216 : BitVec 64).toNat = 16777216 := rfl
  have req16 := alloc_request_of_room P3 16777216 (by rw [e16]; omega)
  have fin16 := allocationEnd_within_heap P3 16777216 (by omega) req16
  have c16 := allocationEnd_covers P3 16777216 (by rw [e16]; omega)
  rw [e16] at c16
  obtain ⟨allocated,setup,aclk,amem,_,acode,aaddr,abe,capA,journalA,counterA,tsA,heapA,globA⟩ :=
    evaluate_stateInit_journal_setup r1 P3 oldCap oldJ oldCount oldTs (rcode.trans (pc1.trans code)) (by omega) rheap
      ((g1 _ (by decide) (by decide) (by decide)).trans hCap) ((g1 _ (by decide) (by decide) (by decide)).trans hJ)
      ((g1 _ (by decide) (by decide) (by decide)).trans hN) ((g1 _ (by decide) (by decide) (by decide)).trans hTs)
      req16 fin16
  set P4 := allocationEnd P3 16777216 with hP4
  let initialized := emptyLocalsHOLFinite allocated
  have runI : evaluateHOLFiniteState r1 stateInitJournalTail =
      (some (.returned (.val (.word (0 : BitVec 64)))),initialized) := by
    rw [stateInitJournalTail_eq_setup,setup]
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,initialized]
  have memI : initialized.memory = post1.memory := amem.trans rmem
  have addrI : initialized.memaddrs = s.memaddrs := aaddr.trans (raddr.trans pa1)
  have domI : ∀ a : BitVec 64, a.toNat < 33806089496 → initialized.memaddrs a := by rw [addrI]; exact domain
  have bsI : initialized.globals.lookup (ofString "bs") = some (.val (.word p0)) := by
    change allocated.globals.lookup _ = _
    rw [globA _ (by decide) (by decide) (by decide) (by decide) (by decide),rglob _ (by decide) (by decide)]
    exact bs1
  -- the block table at bs + 72 is ready in the initialized state
  obtain ⟨T72,cell72,loT,al72,rdy⟩ := bs72_ready_of_built built2 (fun _ => 20) (r := initialized)
    (aaddr.trans raddr) (abe.trans rbe) (acode.trans rcode)
    (fun a _ _ => by rw [memI]) (by rw [memI]) domI P4 heapA (by omega) fin16 c16.2.2
  have ready72 := rdy (fun _ => rfl)
  have n72 : (p0 + BitVec.ofNat 64 72).toNat = p0.toNat + 72 := by
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]; omega),
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  obtain ⟨widths,post,H,run,world,hH,pH,reg,_,_,_⟩ := stateFreshTx_regT9 initialized (fun _ => 20) P4 0 p0 P3 snapshot 0
    (by change allocated.code = _; rw [acode,rcode,pc1]; exact code) heapA tsA bsI journalA counterA
    (by omega) (by omega) domI (by change 380 ≤ allocated.clock; rw [aclk,rclk]; omega) c64.2.2 capA
    (p0 + BitVec.ofNat 64 72) T72 ready72 al72 cell72 (by rw [n72]; omega)
  refine ⟨initialized,P3,P4,T72,widths,post,H,runI,cell72,run,world,hH,pH,reg⟩

#print axioms stateInit_freshTx_regT9
end InitECandidate.Runtime
