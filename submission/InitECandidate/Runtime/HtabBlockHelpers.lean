import InitECandidate.Runtime.HtabBlockInit
import InitECandidate.Runtime.HtabMergeTail
import InitECandidate.Runtime.VmFn_track_ancestor_access
import InitECandidate.Runtime.OriginalPreReadCode
import InitECandidate.Runtime.GlobalsFrameComposition
import InitECandidate.Runtime.PanDiscardNormalBodyMemory
import InitECandidate.Runtime.PanSingleWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def ancStore (k : BitVec 64) (value : ExpHOL 64) : ProgHOL 64 :=
  .store (.op .add [.var .global (ofString "bs"),.const k]) value

def trackAncestorIte : ProgHOL 64 :=
  .ite (.cmp .equal (.load .one (.op .add [.var .global (ofString "bs"),.const 56])) (.const 0))
    (.seq (ancStore 56 (.const 1)) (ancStore 64 (.var .local (ofString "offset"))))
    (.ite (.cmp .lower (.load .one (.op .add [.var .global (ofString "bs"),.const 64])) (.var .local (ofString "offset")))
      (ancStore 64 (.var .local (ofString "offset"))) .skip)

theorem source_trackAncestor_body :
    sourceFunctionBody Guest.guestFn_track_ancestor_access = .seq trackAncestorIte (.return (.const 0)) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem anc_store {F : Type} (s : PanSemStateFiniteExact 64 F) (B k v : BitVec 64) (value : ExpHOL 64)
    (hB : s.globals.lookup (ofString "bs") = some (.val (.word B)))
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) value = some (.val (.word v)))
    (dom : s.memaddrs (B + k)) :
    evaluateHOLFiniteState s (ancStore k value) = (none,sourceWriteWord s (B + k) v) :=
  evaluate_store_word s (B + k) v _ _ (eval_add2 s _ _ _ _ (eval_global_word s _ B hB) (item_eval_const s _)) hv dom

/-- The ancestor-tracking branch writes only the two ancestor cells of the block record. -/
theorem trackAncestorIte_normal {F : Type} (s m : PanSemStateFiniteExact 64 F) (B O : BitVec 64)
    (hB : s.globals.lookup (ofString "bs") = some (.val (.word B)))
    (hO : s.locals.lookup (ofString "offset") = some (.val (.word O)))
    (d56 : s.memaddrs (B + 56)) (d64 : s.memaddrs (B + 64))
    (run : evaluateHOLFiniteState s trackAncestorIte = (none,m)) :
    m.globals = s.globals ∧ m.locals = s.locals ∧ m.memaddrs = s.memaddrs ∧ m.be = s.be ∧ m.code = s.code ∧
      m.clock = s.clock ∧ ∀ x : BitVec 64, x ≠ B + 56 → x ≠ B + 64 → m.memory x = s.memory x := by
  unfold trackAncestorIte at run
  rw [evaluateHOLFiniteState_ite] at run
  split at run
  · split at run
    · -- inner conditional
      rw [evaluateHOLFiniteState_ite] at run
      split at run
      · split at run
        · rw [evaluateHOLFiniteState_skip] at run
          obtain ⟨_,rfl⟩ := Prod.mk.inj run
          exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,fun _ _ _ => rfl⟩
        · rw [anc_store s B 64 O _ hB (item_eval_locals s _ O hO) d64] at run
          obtain ⟨_,rfl⟩ := Prod.mk.inj run
          refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,fun x _ h2 => ?_⟩
          simp only [sourceWriteWord,if_neg h2]
      · simp at run
    · rw [evaluateHOLFiniteState_seq_line780,anc_store s B 56 1 _ hB (item_eval_const s _) d56] at run
      dsimp only at run
      rw [anc_store (sourceWriteWord s (B + 56) 1) B 64 O _ hB (item_eval_locals _ _ O hO) d64] at run
      obtain ⟨_,rfl⟩ := Prod.mk.inj run
      refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,fun x h1 h2 => ?_⟩
      simp only [sourceWriteWord,if_neg h1,if_neg h2]
  · simp at run

#print axioms trackAncestorIte_normal

/-- `track_ancestor_access(offset)` returning: it returns 0, keeps globals, locals-independent metadata and every
word except the two ancestor cells `bs + 56` and `bs + 64`. -/
theorem trackAncestor_body_returned {F : Type} (s post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) (B O : BitVec 64)
    (hB : s.globals.lookup (ofString "bs") = some (.val (.word B)))
    (hO : s.locals.lookup (ofString "offset") = some (.val (.word O)))
    (d56 : s.memaddrs (B + 56)) (d64 : s.memaddrs (B + 64))
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_track_ancestor_access) = (some (.returned v),post)) :
    v = .val (.word 0) ∧ post.globals = s.globals ∧ post.memaddrs = s.memaddrs ∧ post.be = s.be ∧ post.code = s.code ∧
      ∀ x : BitVec 64, x ≠ B + 56 → x ≠ B + 64 → post.memory x = s.memory x := by
  rw [source_trackAncestor_body,evaluateHOLFiniteState_seq_line780] at run
  cases hI : evaluateHOLFiniteState s trackAncestorIte with
  | mk r m =>
    rw [hI] at run
    cases r with
    | some x =>
      exfalso
      obtain ⟨e,_⟩ := Prod.mk.inj run
      have := evaluate_noTopReturn trackAncestorIte (by decide) s v
      rw [hI] at this
      exact this e
    | none =>
      obtain ⟨g,_,a,b,c,_,mem⟩ := trackAncestorIte_normal s m B O hB hO d56 d64 hI
      obtain ⟨ve,pm,pa,pb,pc,pg⟩ := return_const_globals m post 0 v run
      exact ⟨ve,pg.trans g,pa.trans a,pb.trans b,pc.trans c,fun x h1 h2 => by rw [pm,mem x h1 h2]⟩

#print axioms trackAncestor_body_returned

/-- A discarded call `track_ancestor_access(arg)` with a word argument, returning normally: globals, addresses,
endianness, code and locals are kept, and memory changes only at `bs + 56` and `bs + 64`. -/
theorem trackAncestor_call_normal {F : Type} (s post : PanSemStateFiniteExact 64 F) (argument : ExpHOL 64)
    (B O : BitVec 64) (code : s.code = originalRuntimeCode)
    (hB : s.globals.lookup (ofString "bs") = some (.val (.word B)))
    (arg : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [argument] = some [.val (.word O)])
    (d56 : s.memaddrs (B + 56)) (d64 : s.memaddrs (B + 64))
    (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "track_ancestor_access") [argument]) = (none,post)) :
    post.globals = s.globals ∧ post.locals = s.locals ∧ post.memaddrs = s.memaddrs ∧ post.be = s.be ∧
      post.code = s.code ∧ ∀ x : BitVec 64, x ≠ B + 56 → x ≠ B + 64 → post.memory x = s.memory x := by
  have lookup : lookupCodeHOLFinite s.code.lookup (ofString "track_ancestor_access") [.val (.word O)] =
      some (sourceFunctionBody Guest.guestFn_track_ancestor_access,
        HolFiniteMapExact.empty.update (ofString "offset",.val (.word O)),.one) :=
    pan_single_word_lookup s.code.lookup _ _ _ O (by rw [code]; exact vmLookup_track_ancestor_access)
  obtain ⟨value,output,bodyRun,pm,pl⟩ := evaluate_discard_normal_body_memory s post _ _ _ _ _ _ arg lookup run
  obtain ⟨_,og,oa,ob,oc,omem⟩ := trackAncestor_body_returned
    (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "offset",.val (.word O)))) output value B O
    (by exact hB) (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) (by exact d56)
    (by exact d64) bodyRun
  have meta' := evaluateHOLFiniteState_metadata s (.call (some (none,none)) (ofString "track_ancestor_access") [argument])
  rw [run] at meta'
  have frame : OriginalGlobalsFrame (sourceFunctionBody Guest.guestFn_track_ancestor_access) := by
    rw [source_trackAncestor_body]
    exact originalGlobalsFrame_leaf _ (fun _ => rfl)
  have rel := normalRel_apply (normalRel_discard_call (R := Eq) ⟨fun _ => rfl,fun _ _ _ h1 h2 => h1.trans h2⟩
    (ofString "track_ancestor_access") [argument] _ _ _ vmLookup_track_ancestor_access
    (NormalRel.returned (normalRel_of_frame ⟨fun _ => rfl,fun _ _ _ h1 h2 => h1.trans h2⟩ frame))) (X := s)
    (by rw [run]; exact Or.inl rfl) code
  rw [run] at rel
  exact ⟨rel.symm,pl,meta'.2.1,meta'.2.2.1,meta'.1,fun x h1 h2 => by rw [pm]; exact omem x h1 h2⟩

#print axioms trackAncestor_call_normal

def preReadSet : ProgHOL 64 :=
  .call (some (none,none)) (ofString "htab_set")
    [.load .one (.op .add [.var .global (ofString "bs"),.const 72]),.var .local (ofString "addr"),.const 1]

theorem source_recordPreStateRead_body :
    sourceFunctionBody Guest.guestFn_record_pre_state_read = .seq preReadSet (.return (.const 0)) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem preReadSet_args {F : Type} (s : PanSemStateFiniteExact 64 F) (B P A : BitVec 64)
    (hB : s.globals.lookup (ofString "bs") = some (.val (.word B)))
    (hA : s.locals.lookup (ofString "addr") = some (.val (.word A)))
    (d72 : s.memaddrs (B + 72)) (c72 : s.memory (B + 72) = .word P) :
    evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.load .one (.op .add [.var .global (ofString "bs"),.const 72]),.var .local (ofString "addr"),.const 1] =
      some [.val (.word P),.val (.word A),.val (.word 1)] := by
  have e1 := eval_load_word s _ (B + 72) P (eval_add2 s _ _ _ _ (eval_global_word s _ B hB) (item_eval_const s _)) d72 c72
  have e2 := item_eval_locals s _ A hA
  rw [evalListHOLFinite_eq_toExact]
  simp only [evalListHOLExact,e1,e2,item_eval_const]

set_option maxHeartbeats 2000000 in
/-- `record_pre_state_read(addr)` returning: the pre-state read cache (the table at `bs + 72`) is set at `addr`
and stays laid out with the order invariant; every word below the entry heap pointer outside its header and
block is kept; globals are heap-related. -/
theorem recordPreStateRead_body_returned {F : Type} (s post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (B A : BitVec 64) (keyLength P keys stride capacity used values order orderPos count pointer : BitVec 64)
    (bits lo hi : Nat)
    (hB : s.globals.lookup (ofString "bs") = some (.val (.word B)))
    (hA : s.locals.lookup (ofString "addr") = some (.val (.word A)))
    (d72 : s.memaddrs (B + 72)) (c72 : s.memory (B + 72) = .word P)
    (laid : HtabLaid keyLength P keys stride capacity used values order orderPos count bits lo hi s)
    (tables : OrderInv s capacity count used order orderPos) (room : count.toNat < capacity.toNat)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerAligned : pointer.toNat % 8 = 0) (headerBelow : P.toNat + 72 ≤ pointer.toNat)
    (pointerInside : pointer.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → P.toNat ≤ a.toNat → a.toNat < 33806089496 → s.memaddrs a)
    (small : keyLength.toNat ≤ 33806089496) (budget : setBodyCost keyLength capacity count + 1 ≤ s.clock)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_record_pre_state_read) = (some (.returned v),post)) :
    v = .val (.word 0) ∧
      (∃ (capacity' keys' used' values' order' orderPos' count' : BitVec 64) (bits' : Nat) (lo' hi' : Nat),
        HtabLaid keyLength P keys' stride capacity' used' values' order' orderPos' count' bits' lo' hi' post ∧
        OrderInv post capacity' count' used' order' orderPos' ∧
        ((capacity' = capacity ∧ count' = count) ∨ (count'.toNat = count.toNat + 1 ∧ count'.toNat * 2 ≤ capacity'.toNat)) ∧
        ((lo' = lo ∧ hi' = hi) ∨ pointer.toNat ≤ lo')) ∧
      HeapRel s.globals post.globals ∧ post.memaddrs = s.memaddrs ∧ post.be = s.be ∧ post.code = s.code ∧
      (∀ w : BitVec 64, w.toNat < pointer.toNat → (w.toNat < P.toNat ∨ P.toNat + 72 ≤ w.toNat) →
        (w.toNat < lo ∨ hi ≤ w.toNat) → post.memory w = s.memory w) := by
  rw [source_recordPreStateRead_body,evaluateHOLFiniteState_seq_line780] at run
  cases hI : evaluateHOLFiniteState s preReadSet with
  | mk r m =>
    rw [hI] at run
    cases r with
    | some x =>
      exfalso
      obtain ⟨e,_⟩ := Prod.mk.inj run
      have := evaluate_noTopReturn preReadSet (by decide) s v
      rw [hI] at this
      exact this e
    | none =>
      obtain ⟨⟨c',k',u',v',o',op',n',b',lo',hi',laid',tables',r1,_,r3⟩,ml,ma,mb,mframe⟩ :=
        htabSet_call_normal_laid s m _ _ _ keyLength P keys stride capacity used values order orderPos count A 1 pointer
          bits lo hi laid (preReadSet_args s B P A hB hA d72 c72) heap pointerAligned headerBelow pointerInside arena tables
          room small budget hI
      have mc : m.code = s.code := by
        have := evaluateHOLFiniteState_metadata s preReadSet; rw [hI] at this; exact this.1
      have rel := normalRel_apply (htabSet_call_normalRel
        [.load .one (.op .add [.var .global (ofString "bs"),.const 72]),.var .local (ofString "addr"),.const 1]) (X := s)
        (by change Continuing (evaluateHOLFiniteState s preReadSet).1; rw [hI]; exact Or.inl rfl) laid.code
      change HeapRel s.globals (evaluateHOLFiniteState s preReadSet).2.globals at rel
      rw [hI] at rel
      obtain ⟨ve,pm,pa,pb,pc,pg⟩ := return_const_globals m post 0 v run
      obtain ⟨laidP,tablesP⟩ := laid'.congr_tables tables' pa pb pc (fun w _ => by rw [pm])
      exact ⟨ve,⟨c',k',u',v',o',op',n',b',lo',hi',laidP,tablesP,r1,r3⟩,by rw [pg]; exact rel,pa.trans ma,pb.trans mb,
        pc.trans mc,fun w h1 h2 h3 => by rw [pm]; exact mframe w h1 h2 h3⟩

#print axioms recordPreStateRead_body_returned

theorem recordPreStateRead_normalRel : NormalRel HeapRel (sourceFunctionBody Guest.guestFn_record_pre_state_read) := by
  rw [source_recordPreStateRead_body]
  exact normalRel_seq heapRel_preorder (htabSet_call_normalRel _)
    (normalRel_of_frame heapRel_preorder (originalGlobalsFrame_leaf _ (fun _ => rfl)))

set_option maxHeartbeats 2000000 in
/-- A discarded call `record_pre_state_read(arg)` returning normally: the pre-state read cache stays laid out with
the order invariant, locals are kept, globals are heap-related, and every word below the entry heap pointer
outside the cache's header and block is kept. -/
theorem recordPreStateRead_call_normal {F : Type} (s post : PanSemStateFiniteExact 64 F) (argument : ExpHOL 64)
    (B A : BitVec 64) (keyLength P keys stride capacity used values order orderPos count pointer : BitVec 64)
    (bits lo hi : Nat)
    (hB : s.globals.lookup (ofString "bs") = some (.val (.word B)))
    (arg : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [argument] = some [.val (.word A)])
    (d72 : s.memaddrs (B + 72)) (c72 : s.memory (B + 72) = .word P)
    (laid : HtabLaid keyLength P keys stride capacity used values order orderPos count bits lo hi s)
    (tables : OrderInv s capacity count used order orderPos) (room : count.toNat < capacity.toNat)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerAligned : pointer.toNat % 8 = 0) (headerBelow : P.toNat + 72 ≤ pointer.toNat)
    (pointerInside : pointer.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → P.toNat ≤ a.toNat → a.toNat < 33806089496 → s.memaddrs a)
    (small : keyLength.toNat ≤ 33806089496) (budget : setBodyCost keyLength capacity count + 2 ≤ s.clock)
    (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "record_pre_state_read") [argument]) = (none,post)) :
    (∃ (capacity' keys' used' values' order' orderPos' count' : BitVec 64) (bits' : Nat) (lo' hi' : Nat),
        HtabLaid keyLength P keys' stride capacity' used' values' order' orderPos' count' bits' lo' hi' post ∧
        OrderInv post capacity' count' used' order' orderPos' ∧
        ((capacity' = capacity ∧ count' = count) ∨ (count'.toNat = count.toNat + 1 ∧ count'.toNat * 2 ≤ capacity'.toNat)) ∧
        ((lo' = lo ∧ hi' = hi) ∨ pointer.toNat ≤ lo')) ∧
      HeapRel s.globals post.globals ∧ post.locals = s.locals ∧ post.memaddrs = s.memaddrs ∧ post.be = s.be ∧
      post.code = s.code ∧
      (∀ w : BitVec 64, w.toNat < pointer.toNat → (w.toNat < P.toNat ∨ P.toNat + 72 ≤ w.toNat) →
        (w.toNat < lo ∨ hi ≤ w.toNat) → post.memory w = s.memory w) := by
  have code := laid.code
  have lookup : lookupCodeHOLFinite s.code.lookup (ofString "record_pre_state_read") [.val (.word A)] =
      some (sourceFunctionBody Guest.guestFn_record_pre_state_read,
        HolFiniteMapExact.empty.update (ofString "addr",.val (.word A)),.one) :=
    pan_single_word_lookup s.code.lookup _ _ _ A (by rw [code]; exact originalRuntimeCode_recordPreStateRead_lookup)
  obtain ⟨value,output,bodyRun,pm,pl⟩ := evaluate_discard_normal_body_memory s post _ _ _ _ _ _ arg lookup run
  obtain ⟨_,⟨c',k',u',v',o',op',n',b',lo',hi',laid',tables',r1,r3⟩,_,oa,ob,oc,omem⟩ := recordPreStateRead_body_returned
    (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "addr",.val (.word A)))) output value B A
    keyLength P keys stride capacity used values order orderPos count pointer bits lo hi (by exact hB)
    (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) (by exact d72) (by exact c72)
    (laid.congr_tables (r := callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "addr",.val (.word A))))
      tables rfl rfl rfl (fun _ _ => rfl)).1
    (tables.congr (r := callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "addr",.val (.word A))))
      (Nat.le_of_lt room) rfl rfl
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)) room (by exact heap) pointerAligned headerBelow pointerInside
    (fun a h1 h2 h3 => by exact arena a h1 h2 h3) small (by change _ ≤ s.clock - 1; omega) bodyRun
  have meta' := evaluateHOLFiniteState_metadata s (.call (some (none,none)) (ofString "record_pre_state_read") [argument])
  rw [run] at meta'
  have rel := normalRel_apply (normalRel_discard_call heapRel_preorder (ofString "record_pre_state_read") [argument] _ _ _
    originalRuntimeCode_recordPreStateRead_lookup (NormalRel.returned recordPreStateRead_normalRel)) (X := s)
    (by rw [run]; exact Or.inl rfl) code
  rw [run] at rel
  have pa : post.memaddrs = output.memaddrs := meta'.2.1.trans oa.symm
  have pb : post.be = output.be := meta'.2.2.1.trans ob.symm
  have pc : post.code = output.code := meta'.1.trans oc.symm
  obtain ⟨laidP,tablesP⟩ := laid'.congr_tables tables' pa pb pc (fun w _ => by rw [pm])
  exact ⟨⟨c',k',u',v',o',op',n',b',lo',hi',laidP,tablesP,r1,r3⟩,rel,pl,meta'.2.1,meta'.2.2.1,meta'.1,
    fun w h1 h2 h3 => by rw [pm]; exact omem w h1 h2 h3⟩

#print axioms recordPreStateRead_call_normal

/-- Any other laid table whose header and block avoid the two ancestor cells survives `track_ancestor_access`. -/
theorem trackAncestor_call_keeps_table {F : Type} {s post : PanSemStateFiniteExact 64 F} {B : BitVec 64}
    {keyLength t keys stride capacity used values order orderPos count : BitVec 64} {bits lo hi : Nat}
    (laid : HtabLaid keyLength t keys stride capacity used values order orderPos count bits lo hi s)
    (tables : OrderInv s capacity count used order orderPos)
    (frame : post.memaddrs = s.memaddrs ∧ post.be = s.be ∧ post.code = s.code ∧
      ∀ x : BitVec 64, x ≠ B + 56 → x ≠ B + 64 → post.memory x = s.memory x)
    (apart : ∀ w, TZone t lo hi w → w ≠ (B + 56).toNat ∧ w ≠ (B + 64).toNat) :
    HtabLaid keyLength t keys stride capacity used values order orderPos count bits lo hi post ∧
      OrderInv post capacity count used order orderPos :=
  laid.congr_tables tables frame.1 frame.2.1 frame.2.2.1 (fun x h => frame.2.2.2 x
    (fun e => (apart _ (laid.foot_sub _ h)).1 (by rw [e]))
    (fun e => (apart _ (laid.foot_sub _ h)).2 (by rw [e])))

/-- Any other laid table below the entry heap pointer, apart from the cache's header and block, survives
`record_pre_state_read`. -/
theorem recordPreStateRead_keeps_table {F : Type} {s post : PanSemStateFiniteExact 64 F} {P pointer : BitVec 64}
    {lo0 hi0 : Nat} {keyLength t keys stride capacity used values order orderPos count : BitVec 64} {bits lo hi : Nat}
    (laid : HtabLaid keyLength t keys stride capacity used values order orderPos count bits lo hi s)
    (tables : OrderInv s capacity count used order orderPos)
    (ma : post.memaddrs = s.memaddrs) (mb : post.be = s.be) (mc : post.code = s.code)
    (frame : ∀ w : BitVec 64, w.toNat < pointer.toNat → (w.toNat < P.toNat ∨ P.toNat + 72 ≤ w.toNat) →
      (w.toNat < lo0 ∨ hi0 ≤ w.toNat) → post.memory w = s.memory w)
    (apart : ∀ w, TZone t lo hi w → w < pointer.toNat ∧ ¬ TZone P lo0 hi0 w) :
    HtabLaid keyLength t keys stride capacity used values order orderPos count bits lo hi post ∧
      OrderInv post capacity count used order orderPos :=
  laid.congr_tables tables ma mb mc (fun x h => by
    obtain ⟨lt,nz⟩ := apart _ (laid.foot_sub _ h)
    unfold TZone at nz
    exact frame x lt (by omega) (by omega))

#print axioms trackAncestor_call_keeps_table
#print axioms recordPreStateRead_keeps_table
end InitECandidate.Runtime
