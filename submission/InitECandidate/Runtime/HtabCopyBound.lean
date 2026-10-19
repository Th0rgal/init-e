import InitECandidate.Runtime.HtabUnionMerge
import InitECandidate.Runtime.HtabCopyFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-! All-outcome runtime of `htab_copy`: from only the capacity and stride header words, the body
(and the call) spend at most `htabCopyAllCost` (+1) ticks in every outcome, including allocation
traps and unmapped source cells; `htabCopyAllCost ≤ htabCopyCost`. -/

/-- A discarded call that finishes normally restores the caller's locals and keeps the code. -/
theorem discard_call_normal_locals {F : Type} (s post : PanSemStateFiniteExact 64 F) (function : MlS)
    (arguments : List (ExpHOL 64))
    (run : evaluateHOLFiniteState s (.call (some (none,none)) function arguments) = (none,post)) :
    post.locals = s.locals := by
  cases args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments with
  | none => rw [evaluateHOLFiniteState_call,args] at run; simp at run
  | some values =>
    cases lookup : lookupCodeHOLFinite s.code.lookup function values with
    | none => rw [evaluateHOLFiniteState_call,args] at run; simp only at run; rw [lookup] at run; simp at run
    | some found =>
      obtain ⟨body,callee,shape⟩ := found
      obtain ⟨_,_,_,_,l,_⟩ := evaluate_discard_normal_body_globals s post function arguments values body callee shape args
        lookup run
      exact l

/-- memcpy with a word destination local, a word size, and a source loaded from a header cell
(mapped or not) costs size/32 + size/8 + 11 in every outcome. -/
theorem runBounded_memcpy_loaded {F : Type} (s : PanSemStateFiniteExact 64 F) (name : MlS) (sizeArg : ExpHOL 64)
    (T srcOff p N : BitVec 64)
    (nameL : s.locals.lookup name = some (.val (.word p)))
    (tL : s.locals.lookup (ofString "t") = some (.val (.word T)))
    (sizeEval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) sizeArg =
      some (.val (.word N)))
    (code : s.code = originalRuntimeCode) (small : N.toNat ≤ 33806089496)
    (budget : N.toNat / 32 + N.toNat / 8 + 11 ≤ s.clock) :
    RunBounded s (.call (some (none,none)) (ofString "memcpy")
      [.var .local name,.load .one (hashLocalAddress (ofString "t") srcOff),sizeArg]) (N.toNat / 32 + N.toNat / 8 + 11) := by
  by_cases dom : s.memaddrs (T + srcOff)
  · obtain ⟨w,cell⟩ := memory_cell_word s (T + srcOff)
    have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.var .local name,.load .one (hashLocalAddress (ofString "t") srcOff),sizeArg] =
        some [.val (.word p),.val (.word w),.val (.word N)] := by
      rw [evalListHOLFinite_eq_toExact]
      simp only [evalListHOLExact,eval_header_load s _ T srcOff w tL dom cell,sizeEval]
      simp [evalHOLExact,nameL]
    have b := evaluate_memcpy_call_bounded s _ p w N args code small budget
    exact ⟨b.1,b.2.1,b.2.2⟩
  · have none' : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.var .local name,.load .one (hashLocalAddress (ofString "t") srcOff),sizeArg] = none := by
      rw [evalListHOLFinite_eq_toExact]
      simp [evalListHOLExact,evalHOLExact,isWfShapeExactHOL,hashLocalAddress,evalListHOLExact,tL,nameL,wordOpHOL,wordOp,
        valueIsWord,valueWord,memLoadHOLExact,dom]
    unfold RunBounded
    rw [evaluateHOLFiniteState_call,none']
    simp

#print axioms runBounded_memcpy_loaded

/-- One copy phase `name = alloc(size); memcpy(name, lds(t+srcOff), size); st n+storeOff, name; tail`
costs its allocation, its memcpy and the tail in every outcome. -/
theorem runBounded_copy_phase {F : Type} (s : PanSemStateFiniteExact 64 F) (name : MlS) (sizeArg : ExpHOL 64)
    (srcOff storeOff : BitVec 64) (tail : ProgHOL 64) (tailCost : Nat) (T p N : BitVec 64)
    (code : s.code = originalRuntimeCode)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p))) (pIn : p.toNat ≤ 33806089496)
    (nameT : name ≠ ofString "t") (tL : s.locals.lookup (ofString "t") = some (.val (.word T)))
    (sizeEval : ∀ r : PanSemStateFiniteExact 64 F, (∀ k, k ≠ name → r.locals.lookup k = s.locals.lookup k) →
      @evalHOLExact 64 F _ r.toExact (fun a => Classical.propDecidable (r.memaddrs a)) sizeArg = some (.val (.word N)))
    (budget : 1 + 1 + ((N.toNat / 32 + N.toNat / 8 + 11) + (0 + tailCost)) ≤ s.clock)
    (tailB : ∀ r : PanSemStateFiniteExact 64 F, r.code = originalRuntimeCode →
      (∀ k, k ≠ name → r.locals.lookup k = s.locals.lookup k) →
      (∃ q : BitVec 64, r.globals.lookup (ofString "heap_ptr") = some (.val (.word q)) ∧ q.toNat ≤ 33806089496) →
      tailCost ≤ r.clock → RunBounded r tail tailCost) :
    RunBounded s (.decCall name .one (ofString "alloc") [sizeArg]
      (.seq (.call (some (none,none)) (ofString "memcpy")
          [.var .local name,.load .one (hashLocalAddress (ofString "t") srcOff),sizeArg])
        (.seq (.store (hashLocalAddress (ofString "n") storeOff) (.var .local name)) tail)))
      (1 + 1 + ((N.toNat / 32 + N.toNat / 8 + 11) + (0 + tailCost))) := by
  refine runBounded_alloc_decCall s name sizeArg _ p N
    (by rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,sizeEval s (fun _ _ => rfl)]) code heap budget ?_
  intro r rN rO rm ra rb rc rH req fin tc
  have lay := alloc_step_layout p N pIn req
  refine RunBounded.seq (runBounded_memcpy_loaded r name sizeArg T srcOff p N rN
    (by rw [rO _ (Ne.symm nameT)]; exact tL) (sizeEval r rO) (rc.trans code) (by omega) (by omega)) (by omega) ?_
  intro next run1 nextCode _
  have nl := discard_call_normal_locals r next _ _ run1
  have hr := normalRel_apply (normalRel_discard_call heapRel_preorder _ _ _ _ _ originalRuntimeCode_memcpy_lookup
    memcpy_returnedRel) (X := r) (by rw [run1]; exact Or.inl rfl) (rc.trans code)
  rw [run1] at hr
  obtain ⟨q1,hq1,_,qa1,qi1⟩ := hr.2 _ rH lay.2.1 fin
  have nCode : next.code = originalRuntimeCode := nextCode.trans (rc.trans code)
  refine RunBounded.seq (RunBounded.ofProg (ProgBounded.straight _ rfl) nCode (Nat.zero_le _)) (by omega) ?_
  intro next2 run2 code2 clk2
  have sl := (evaluate_store_control_frame next (hashLocalAddress (ofString "n") storeOff) (.var .local name)).2.1
  rw [run2] at sl
  have hs := normalRel_apply (heapRel_leaf (program := .store (hashLocalAddress (ofString "n") storeOff) (.var .local name))
    (fun _ => rfl)) (X := next) (by rw [run2]; exact Or.inl rfl) nCode
  rw [run2] at hs
  obtain ⟨q2,hq2,_,_,qi2⟩ := hs.2 q1 hq1 qa1 qi1
  exact tailB next2 (code2.trans nCode) (fun k ne => by rw [sl,nl,rO k ne]) ⟨q2,hq2,qi2⟩ clk2

#print axioms runBounded_copy_phase

/-- The exact all-outcome cost of `htab_copy`: six allocations and six copies. -/
def htabCopyAllCost (capacity stride : BitVec 64) : Nat :=
  1 + 1 + (((72 : BitVec 64).toNat / 32 + (72 : BitVec 64).toNat / 8 + 11) + (1 + 1 + (((capacity * stride).toNat / 32 + (capacity * stride).toNat / 8 + 11) + (0 + (1 + 1 + (((capacity * 8).toNat / 32 + (capacity * 8).toNat / 8 + 11) + (0 + (1 + 1 + (((capacity).toNat / 32 + (capacity).toNat / 8 + 11) + (0 + (1 + 1 + (((capacity * 8).toNat / 32 + (capacity * 8).toNat / 8 + 11) + (0 + (1 + 1 + (((capacity * 8).toNat / 32 + (capacity * 8).toNat / 8 + 11) + (0 + 0))))))))))))))))

theorem htabCopyAllCost_le (capacity stride : BitVec 64) : htabCopyAllCost capacity stride ≤ htabCopyCost capacity stride := by
  have m1 : (capacity * stride).toNat ≤ capacity.toNat * stride.toNat := by
    rw [BitVec.toNat_mul]; exact Nat.mod_le _ _
  have m2 : (capacity * 8).toNat ≤ capacity.toNat * 8 := by
    rw [BitVec.toNat_mul]; exact Nat.mod_le _ _
  have e72 : (72 : BitVec 64).toNat = 72 := rfl
  unfold htabCopyAllCost htabCopyCost
  rw [e72]
  generalize (capacity * stride).toNat = a at *
  generalize (capacity * 8).toNat = b at *
  generalize capacity.toNat * stride.toNat = c at *
  generalize capacity.toNat = d at *
  omega

#print axioms htabCopyAllCost_le

structure CopyLocals {F : Type} (r : PanSemStateFiniteExact 64 F) (T capacity stride : BitVec 64) : Prop where
  t : r.locals.lookup (ofString "t") = some (.val (.word T))
  cap : r.locals.lookup (ofString "cap") = some (.val (.word capacity))
  stride : r.locals.lookup (ofString "stride") = some (.val (.word stride))

theorem CopyLocals.keep {F : Type} {r s : PanSemStateFiniteExact 64 F} {T capacity stride : BitVec 64} {name : MlS}
    (l : CopyLocals s T capacity stride) (nt : name ≠ ofString "t") (nc : name ≠ ofString "cap")
    (ns : name ≠ ofString "stride") (same : ∀ k, k ≠ name → r.locals.lookup k = s.locals.lookup k) :
    CopyLocals r T capacity stride :=
  ⟨(same _ (Ne.symm nt)).trans l.t,(same _ (Ne.symm nc)).trans l.cap,(same _ (Ne.symm ns)).trans l.stride⟩

theorem CopyLocals.eval_capStride {F : Type} {r : PanSemStateFiniteExact 64 F} {T capacity stride : BitVec 64}
    (l : CopyLocals r T capacity stride) :
    @evalHOLExact 64 F _ r.toExact (fun a => Classical.propDecidable (r.memaddrs a))
      (.panop .mul [.var .local (ofString "cap"),.var .local (ofString "stride")]) =
      some (.val (.word (capacity * stride))) :=
  eval_mul2 r _ _ capacity stride (item_eval_locals r _ _ l.cap) (item_eval_locals r _ _ l.stride)

theorem CopyLocals.eval_cap8 {F : Type} {r : PanSemStateFiniteExact 64 F} {T capacity stride : BitVec 64}
    (l : CopyLocals r T capacity stride) :
    @evalHOLExact 64 F _ r.toExact (fun a => Classical.propDecidable (r.memaddrs a))
      (.panop .mul [.var .local (ofString "cap"),.const 8]) = some (.val (.word (capacity * 8))) :=
  eval_mul2 r _ _ capacity 8 (item_eval_locals r _ _ l.cap) (item_eval_const r 8)

set_option maxHeartbeats 2000000 in
/-- The original `htab_copy` body spends at most htabCopyAllCost ticks in every outcome (allocation
traps, unmapped header cells and memory errors included), given only the two header words it sizes by. -/
theorem evaluate_htabCopy_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F) (T capacity stride p : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (tL : state.locals.lookup (ofString "t") = some (.val (.word T)))
    (c16 : state.memory (T + 16) = .word capacity) (c8 : state.memory (T + 8) = .word stride)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word p))) (pIn : p.toNat ≤ 33806089496)
    (budget : htabCopyAllCost capacity stride ≤ state.clock) :
    RunBounded state (sourceFunctionBody Guest.guestFn_htab_copy) (htabCopyAllCost capacity stride) := by
  unfold htabCopyAllCost at budget ⊢
  rw [source_htabCopy_body]
  refine RunBounded.dec state _ _ _ (fun v1 e1 => ?_)
  rw [eval_load_word_some state _ (T + 16) (eval_hashLocalAddress state _ T 16 tL) v1 e1,c16]
  refine RunBounded.dec _ _ _ _ (fun v2 e2 => ?_)
  have tL1 : (setVarHOLFinite (ofString "cap") (.val (.word capacity)) state).locals.lookup (ofString "t") =
      some (.val (.word T)) := by
    simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tL]
  rw [eval_load_word_some _ _ (T + 8) (eval_hashLocalAddress _ _ T 8 tL1) v2 e2]
  change RunBounded (setVarHOLFinite (ofString "stride") (.val (state.memory (T + 8)))
    (setVarHOLFinite (ofString "cap") (.val (.word capacity)) state)) _ _
  rw [c8]
  generalize hs : setVarHOLFinite (ofString "stride") (.val (.word stride))
    (setVarHOLFinite (ofString "cap") (.val (.word capacity)) state) = s at *
  have sL : CopyLocals s T capacity stride := by
    rw [← hs]
    exact ⟨by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,tL],
      by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],
      by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]⟩
  have sCode : s.code = originalRuntimeCode := by rw [← hs]; exact code
  have sHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) := by rw [← hs]; exact heap
  have sClock : s.clock = state.clock := by rw [← hs]; rfl
  -- header phase: n = alloc(72); memcpy(n, t, 72)
  refine runBounded_alloc_decCall s (ofString "n") (.const 72) _ p 72 (by rw [evalListHOLFinite_eq_toExact]; rfl)
    sCode sHeap (by omega) ?_
  intro r rN rO _ _ _ rc rH req fin tc
  have lay := alloc_step_layout p 72 pIn req
  have rL := sL.keep (by decide) (by decide) (by decide) rO
  have hArgs : evalListHOLFinite r (h := fun a => Classical.propDecidable (r.memaddrs a))
      [.var .local (ofString "n"),.var .local (ofString "t"),.const 72] =
      some [.val (.word p),.val (.word T),.val (.word 72)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,rN,rL.t]
  have hb := evaluate_memcpy_call_bounded r _ p T 72 hArgs (rc.trans sCode) (by decide) (by omega)
  refine RunBounded.seq ⟨hb.1,hb.2.1,hb.2.2⟩ (by omega) ?_
  intro r0 run0 code0 _
  have nl0 := discard_call_normal_locals r r0 _ _ run0
  have hr := normalRel_apply (normalRel_discard_call heapRel_preorder _ _ _ _ _ originalRuntimeCode_memcpy_lookup
    memcpy_returnedRel) (X := r) (by rw [run0]; exact Or.inl rfl) (rc.trans sCode)
  rw [run0] at hr
  obtain ⟨q0,hq0,_,_,qi0⟩ := hr.2 _ rH lay.2.1 fin
  have l0 : CopyLocals r0 T capacity stride := rL.keep (name := ofString "n") (by decide) (by decide) (by decide)
    (fun k _ => by rw [nl0])
  have c0 : r0.code = originalRuntimeCode := code0.trans (rc.trans sCode)
  -- keys
  refine runBounded_copy_phase r0 (ofString "keys") _ 32 32 _ _ T q0 (capacity * stride) c0 hq0 qi0 (by decide) l0.t
    (fun r' same => (l0.keep (by decide) (by decide) (by decide) same).eval_capStride) (by assumption) ?_
  intro r1 c1 o1 ⟨q1,hq1,qi1⟩ tc1
  have l1 := l0.keep (by decide) (by decide) (by decide) o1
  -- vals
  refine runBounded_copy_phase r1 (ofString "vals") _ 40 40 _ _ T q1 (capacity * 8) c1 hq1 qi1 (by decide) l1.t
    (fun r' same => (l1.keep (by decide) (by decide) (by decide) same).eval_cap8) tc1 ?_
  intro r2 c2 o2 ⟨q2,hq2,qi2⟩ tc2
  have l2 := l1.keep (by decide) (by decide) (by decide) o2
  -- used
  refine runBounded_copy_phase r2 (ofString "used") _ 48 48 _ _ T q2 capacity c2 hq2 qi2 (by decide) l2.t
    (fun r' same => item_eval_locals r' _ _ (l2.keep (by decide) (by decide) (by decide) same).cap) tc2 ?_
  intro r3 c3 o3 ⟨q3,hq3,qi3⟩ tc3
  have l3 := l2.keep (by decide) (by decide) (by decide) o3
  -- order
  refine runBounded_copy_phase r3 (ofString "order") _ 56 56 _ _ T q3 (capacity * 8) c3 hq3 qi3 (by decide) l3.t
    (fun r' same => (l3.keep (by decide) (by decide) (by decide) same).eval_cap8) tc3 ?_
  intro r4 c4 o4 ⟨q4,hq4,qi4⟩ tc4
  have l4 := l3.keep (by decide) (by decide) (by decide) o4
  -- order_pos
  refine runBounded_copy_phase r4 (ofString "order_pos") _ 64 64 _ _ T q4 (capacity * 8) c4 hq4 qi4 (by decide) l4.t
    (fun r' same => (l4.keep (by decide) (by decide) (by decide) same).eval_cap8) tc4 ?_
  intro r5 c5 _ _ _
  exact RunBounded.ofProg (ProgBounded.straight _ (by decide)) c5 (Nat.zero_le _)

#print axioms evaluate_htabCopy_body_bounded

/-- The `htab_copy(t)` call costs at most htabCopyAllCost + 1 ticks in every outcome. -/
theorem runBounded_htabCopy_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (tableArgument : ExpHOL 64) (T capacity stride p : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [tableArgument] =
      some [.val (.word T)])
    (c16 : state.memory (T + 16) = .word capacity) (c8 : state.memory (T + 8) = .word stride)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word p))) (pIn : p.toNat ≤ 33806089496)
    (budget : htabCopyAllCost capacity stride + 1 ≤ state.clock) :
    RunBounded state (.call (some (destination,none)) (ofString "htab_copy") [tableArgument])
      (htabCopyAllCost capacity stride + 1) := by
  refine RunBounded.call args budget ?_
  intro body locals returnShape lookup
  rw [htabCopy_installed state T code] at lookup
  simp only [Option.some.injEq,Prod.mk.injEq] at lookup
  obtain ⟨rfl,rfl,rfl⟩ := lookup
  exact evaluate_htabCopy_body_bounded _ T capacity stride p (by exact code)
    (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) (by exact c16) (by exact c8)
    (by exact heap) pIn (by change _ ≤ state.clock - 1; omega)

#print axioms runBounded_htabCopy_call
end InitECandidate.Runtime
