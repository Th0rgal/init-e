import InitECandidate.Runtime.KeccakWindow
import InitECandidate.Runtime.OriginalAllocationCode
import InitECandidate.Runtime.AllocationSuccess
import InitECandidate.Runtime.VmFn_heap_mark
import InitECandidate.Runtime.VmFn_heap_release
import InitECandidate.Runtime.PanNoArgsLookup
import InitECandidate.Runtime.MptReadFrame
import InitECandidate.Runtime.PanTwoWordShapeLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A declared call keeps a watched word in every outcome if the looked-up body keeps it from the callee entry
state, and the continuation keeps it from every resumed state after a return. -/
theorem decCall_watch {F : Type} (s : PanSemStateFiniteExact 64 F) (name function : MlS) (shape : ShapeHOL)
    (arguments : List (ExpHOL 64)) (cont : ProgHOL 64) (w : BitVec 64)
    (hbody : ∀ values body callee rs,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite s.code.lookup function values = some (body,callee,rs) →
      (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).2.memory w = s.memory w)
    (hcont : ∀ values body callee rs v (post : PanSemStateFiniteExact 64 F),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite s.code.lookup function values = some (body,callee,rs) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v),post) →
      ∀ resumed : PanSemStateFiniteExact 64 F, resumed.memory = post.memory → resumed.globals = post.globals →
        resumed.code = post.code → resumed.memaddrs = post.memaddrs → resumed.be = post.be →
        resumed.locals = s.locals.update (name,v) →
        (evaluateHOLFiniteState resumed cont).2.memory w = s.memory w) :
    (evaluateHOLFiniteState s (.decCall name shape function arguments cont)).2.memory w = s.memory w := by
  rw [evaluateHOLFiniteState_decCall_total]
  cases args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments with
  | none => rfl
  | some values =>
    dsimp only
    cases lookup : lookupCodeHOLFinite s.code.lookup function values with
    | none => rfl
    | some data =>
      obtain ⟨body,callee,rs⟩ := data
      dsimp only
      split
      · rfl
      · have hb := hbody values body callee rs args lookup
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk r post =>
          rw [bodyRun] at hb
          change post.memory w = s.memory w at hb
          dsimp only [fixClockHOLFinite]
          cases r with
          | none => exact hb
          | some r =>
            cases r with
            | returned v =>
              dsimp only
              split
              · exact hcont values body callee rs v post args lookup bodyRun _ rfl rfl rfl rfl rfl rfl
              · exact hb
            | _ => exact hb

#print axioms decCall_watch

/-- A discarded call keeps a watched word in every outcome if its looked-up body keeps it from the callee entry. -/
theorem memWatch_discardCall {F : Type} (state : PanSemStateFiniteExact 64 F) (w : BitVec 64) (function : MlS)
    (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments = some values)
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (bodyWatch : (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2.memory w = state.memory w) :
    (evaluateHOLFiniteState state (.call (some (none,none)) function arguments)).2.memory w = state.memory w := by
  rw [evaluateHOLFiniteState_call,args]
  dsimp only
  rw [lookup]
  dsimp only
  split
  · simp [emptyLocalsHOLFinite]
  · cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
    | mk rb bodyPost =>
      rw [bodyRun] at bodyWatch
      change bodyPost.memory w = state.memory w at bodyWatch
      rcases rb with _ | (_ | _ | _ | _ | v | _ | _)
      all_goals (dsimp only; try split)
      all_goals exact bodyWatch

theorem evaluate_assign_memory {F : Type} (s : PanSemStateFiniteExact 64 F) (k : VarKind) (n : MlS) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.assign k n e)).2.memory = s.memory := by
  rw [evaluateHOLFiniteState_assign]
  split
  · rfl
  · split
    · cases k <;> rfl
    · rfl

theorem source_heapRelease_body : sourceFunctionBody Guest.guestFn_heap_release =
    .seq (.assign .global (ofString "heap_ptr") (.var .local (ofString "m"))) (.return (.const 0)) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem heapRelease_body_memory {F : Type} (E : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState E (sourceFunctionBody Guest.guestFn_heap_release)).2.memory = E.memory := by
  rw [source_heapRelease_body,evaluateHOLFiniteState_seq_line780]
  have h := evaluate_assign_memory E .global (ofString "heap_ptr") (.var .local (ofString "m"))
  cases r : evaluateHOLFiniteState E (.assign .global (ofString "heap_ptr") (.var .local (ofString "m"))) with
  | mk res m =>
    rw [r] at h
    cases res with
    | some x => exact h
    | none => exact (evaluate_readOnly_memory (.return (.const 0)) (by decide) m).trans h

theorem source_heapMark_body : sourceFunctionBody Guest.guestFn_heap_mark =
    .return (.var .global (ofString "heap_ptr")) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms memWatch_discardCall
#print axioms heapRelease_body_memory

def wsAccountLeafHOL : ProgHOL 64 := (.decCall (ofString "mark") .one (ofString "heap_mark") [] (.decCall (ofString "h") .one (ofString "alloc") [(.const 32)] (.seq (.call (some (none,none)) (ofString "keccak256") [(.var .local (ofString "addr")),(.const 20),(.var .local (ofString "h"))]) (.decCall (ofString "r") (.comb [.one,.one,.one]) (ofString "trie_lookup") [(.load .one (.op .add [(.var .global (ofString "ws")),(.const 24)])),(.var .local (ofString "h"))] (.seq (.call (some (none,none)) (ofString "heap_release") [(.var .local (ofString "mark"))]) (.return (.var .local (ofString "r"))))))))

theorem source_wsAccountLeaf_hol : sourceFunctionBody Guest.guestFn_ws_account_leaf = wsAccountLeafHOL := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

set_option maxHeartbeats 8000000 in
/-- The original `ws_account_leaf(addr)` keeps every word outside the Keccak state and pad, the 32-byte hash block
it allocates at the entry heap pointer, and the nibble scratch buffer, in every outcome (including `MptErr` from
the trie walk); the block fits the heap by the explicit reservation premise. -/
theorem wsAccountLeaf_body_window {F : Type} (s : PanSemStateFiniteExact 64 F) (A P0 K Pd NB w : BitVec 64)
    (code : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "addr") = some (.val (.word A)))
    (hheap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word P0)))
    (hK : s.globals.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd : s.globals.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB : s.globals.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (req : (32 : BitVec 64) ≤ (33806089496 : BitVec 64) - P0)
    (fin : (allocationEnd P0 32).toNat ≤ 33806089496)
    (oK : ¬ MWin K 200 w) (oP : ¬ MWin Pd 136 w) (oH : ¬ MWin P0 32 w)
    (oN : ∀ j : Nat, j < 64 → w ≠ panByteAlignHOL (NB + BitVec.ofNat 64 j)) :
    (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_ws_account_leaf)).2.memory w = s.memory w := by
  rw [source_wsAccountLeaf_hol]
  unfold wsAccountLeafHOL
  have noArgs : ∀ values, evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [] = some values →
      values = [] := by
    intro values h; rw [evalListHOLFinite_eq_toExact] at h; simp [evalListHOLExact] at h; exact h
  have markLookup := pan_no_args_lookup s.code.lookup (ofString "heap_mark") _
    (by rw [code]; exact vmLookup_heap_mark)
  apply decCall_watch
  · intro values body callee rs hargs hl
    rw [noArgs values hargs,markLookup] at hl
    simp only [Option.some.injEq,Prod.mk.injEq] at hl
    obtain ⟨rfl,rfl,rfl⟩ := hl
    rw [source_heapMark_body]
    exact congrFun (evaluate_readOnly_memory _ (by decide) _) w
  · intro values body callee rs v post hargs hl bodyRun r1 m1 g1 c1 a1 b1 l1
    rw [noArgs values hargs,markLookup] at hl
    simp only [Option.some.injEq,Prod.mk.injEq] at hl
    obtain ⟨rfl,rfl,rfl⟩ := hl
    rw [source_heapMark_body,evaluateHOLFiniteState_return] at bodyRun
    have e : @evalHOLExact 64 F _ (callEntryStateHOLFinite s HolFiniteMapExact.empty).toExact
        (fun a => Classical.propDecidable ((callEntryStateHOLFinite s HolFiniteMapExact.empty).memaddrs a))
        (.var .global (ofString "heap_ptr")) = some (.val (.word P0)) := by
      simp [evalHOLExact,callEntryStateHOLFinite,hheap]
    rw [e] at bodyRun
    simp [shapeOfHOLExact] at bodyRun
    obtain ⟨rfl,rfl⟩ := bodyRun
    have rm : r1.memory = s.memory := m1
    have rg : r1.globals = s.globals := g1
    have rc : r1.code = originalRuntimeCode := c1.trans code
    have ra : r1.memaddrs = s.memaddrs := a1
    rw [show s.memory w = r1.memory w by rw [rm]]
    have allocArgs : ∀ values, evalListHOLFinite r1 (h := fun a => Classical.propDecidable (r1.memaddrs a)) [.const 32] =
        some values → values = [.val (.word 32)] := by
      intro values h; rw [evalListHOLFinite_eq_toExact] at h; simp [evalListHOLExact,evalHOLExact] at h; exact h.symm
    have allocLookup := pan_single_word_lookup r1.code.lookup (ofString "alloc") (ofString "n") _ 32
      (by rw [rc]; exact originalRuntimeCode_allocation_lookup)
    have E2heap : (callEntryStateHOLFinite r1 (HolFiniteMapExact.empty.update (ofString "n",.val (.word 32)))).globals.lookup
        (ofString "heap_ptr") = some (.val (.word P0)) := by
      change r1.globals.lookup _ = _; rw [rg]; exact hheap
    have E2n : (callEntryStateHOLFinite r1 (HolFiniteMapExact.empty.update (ofString "n",.val (.word 32)))).locals.lookup
        (ofString "n") = some (.val (.word 32)) := by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    obtain ⟨post2,run2,_,_,mem2,code2,addr2,_,_,glob2⟩ := evaluate_source_alloc_success _ P0 32 E2heap E2n req fin
    apply decCall_watch
    · intro values body callee rs hargs hl
      rw [allocArgs values hargs,allocLookup] at hl
      simp only [Option.some.injEq,Prod.mk.injEq] at hl
      obtain ⟨rfl,rfl,rfl⟩ := hl
      rw [run2]; exact congrFun mem2 w
    · intro values body callee rs v2 post2' hargs hl bodyRun2 r2 m2 g2 c2 a2 b2 l2
      rw [allocArgs values hargs,allocLookup] at hl
      simp only [Option.some.injEq,Prod.mk.injEq] at hl
      obtain ⟨rfl,rfl,rfl⟩ := hl
      rw [run2] at bodyRun2
      simp only [Prod.mk.injEq,Option.some.injEq,PanSemResultExact.returned.injEq] at bodyRun2
      obtain ⟨rfl,rfl⟩ := bodyRun2
      have r2m : r2.memory = r1.memory := m2.trans mem2
      have r2c : r2.code = originalRuntimeCode := c2.trans (code2.trans rc)
      have r2a : r2.memaddrs = r1.memaddrs := a2.trans addr2
      have r2g : ∀ name, name ≠ ofString "heap_ptr" → r2.globals.lookup name = s.globals.lookup name := by
        intro name hne
        rw [g2,glob2]
        simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm hne,callEntryStateHOLFinite,rg]
      have r2loc : ∀ name, name ≠ ofString "h" → name ≠ ofString "mark" → r2.locals.lookup name = s.locals.lookup name := by
        intro name h1 h2
        rw [l2,l1]
        simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm h1,Ne.symm h2]
      have r2h : r2.locals.lookup (ofString "h") = some (.val (.word P0)) := by
        rw [l2]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
      have r2mark : r2.locals.lookup (ofString "mark") = some (.val (.word P0)) := by
        rw [l2,l1]
        have : ofString "h" ≠ ofString "mark" := by decide
        simp [HolFiniteMapExact.lookup_update,FUPDATE,this]
      rw [show r1.memory w = r2.memory w by rw [r2m]]
      -- keccak256(addr, 20, h)
      have kArgs : evalListHOLFinite r2 (h := fun a => Classical.propDecidable (r2.memaddrs a))
          [.var .local (ofString "addr"),.const 20,.var .local (ofString "h")] =
          some [.val (.word A),.val (.word 20),.val (.word P0)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact,evalHOLExact,r2loc (ofString "addr") (by decide) (by decide),ha,r2h]
      have kLookup := pan_three_word_lookup r2.code.lookup (ofString "keccak256") (ofString "p") (ofString "n")
        (ofString "out") _ A 20 P0 (by decide) (by decide) (by decide) (by rw [r2c]; exact originalRuntimeCode_keccak_lookup)
      have kw := watch_discardCall r2 w _ _ _ kArgs _ _ _ kLookup
        ⟨keccak_short_body_window _ A 20 P0 K Pd w (by exact r2c)
          (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
          (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
          (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
          (by change r2.globals.lookup _ = _; rw [r2g _ (by decide)]; exact hK)
          (by change r2.globals.lookup _ = _; rw [r2g _ (by decide)]; exact hPd)
          (by decide) oK oP oH,
         keccak_body_globals_frame _ (by exact r2c)⟩
      rw [evaluateHOLFiniteState_seq_line780]
      cases r3run : evaluateHOLFiniteState r2 (.call (some (none,none)) (ofString "keccak256")
          [.var .local (ofString "addr"),.const 20,.var .local (ofString "h")]) with
      | mk res3 r3 =>
        rw [r3run] at kw
        cases res3 with
        | some x => exact kw.1
        | none =>
          dsimp only
          obtain ⟨_,_,_,_,r3loc⟩ := evaluate_discard_normal_body_memory r2 r3 _ _ _ _ _ _ kArgs kLookup r3run
          have meta3 := evaluateHOLFiniteState_metadata r2 (.call (some (none,none)) (ofString "keccak256")
            [.var .local (ofString "addr"),.const 20,.var .local (ofString "h")])
          rw [r3run] at meta3
          have r3c : r3.code = originalRuntimeCode := meta3.1.trans r2c
          rw [← kw.1]
          have r3h : r3.locals.lookup (ofString "h") = some (.val (.word P0)) := by rw [r3loc]; exact r2h
          have tlArgs : ∀ values, evalListHOLFinite r3 (h := fun a => Classical.propDecidable (r3.memaddrs a))
              [.load .one (.op .add [.var .global (ofString "ws"),.const 24]),.var .local (ofString "h")] = some values →
              ∃ R : BitVec 64, values = [.val (.word R),.val (.word P0)] := by
            intro values h
            rw [evalListHOLFinite_eq_toExact] at h
            have e2 : @evalHOLExact 64 F _ r3.toExact (fun a => Classical.propDecidable (r3.memaddrs a))
                (.var .local (ofString "h")) = some (.val (.word P0)) := by simp [evalHOLExact,r3h]
            cases hl : @evalHOLExact 64 F _ r3.toExact (fun a => Classical.propDecidable (r3.memaddrs a))
                (.load .one (.op .add [.var .global (ofString "ws"),.const 24])) with
            | none => simp only [evalListHOLExact,hl] at h; cases h
            | some x =>
              obtain ⟨R,rfl⟩ := isWord_load r3 _ x hl
              refine ⟨R,?_⟩
              simp only [evalListHOLExact,hl,e2,Option.some.injEq] at h
              exact h.symm
          have tlLookup := fun R => pan_two_word_lookup_shape r3.code.lookup (ofString "trie_lookup") (ofString "root")
            (ofString "key_hash32") _ _ R P0 (by decide) (by rw [r3c]; exact originalRuntimeCode_trieLookup_lookup)
          have tlWin := fun R => (trieLookup_body_window (callEntryStateHOLFinite r3
              ((HolFiniteMapExact.empty.update (ofString "root",.val (.word R))).update (ofString "key_hash32",.val (.word P0))))
            P0 NB w (by exact r3c) (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
            (by change r3.globals.lookup _ = _; rw [kw.2,r2g _ (by decide)]; exact hNB) oN).1
          apply decCall_watch
          · intro values body callee rs hargs hl
            obtain ⟨R,rfl⟩ := tlArgs values hargs
            rw [tlLookup R] at hl
            simp only [Option.some.injEq,Prod.mk.injEq] at hl
            obtain ⟨rfl,rfl,rfl⟩ := hl
            exact tlWin R
          · intro values body callee rs v4 post4 hargs hl bodyRun4 r4 m4 g4 c4 a4 b4 l4
            obtain ⟨R,rfl⟩ := tlArgs values hargs
            rw [tlLookup R] at hl
            simp only [Option.some.injEq,Prod.mk.injEq] at hl
            obtain ⟨rfl,rfl,rfl⟩ := hl
            have W := tlWin R
            rw [bodyRun4] at W
            have meta4 := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite r3
              ((HolFiniteMapExact.empty.update (ofString "root",.val (.word R))).update (ofString "key_hash32",.val (.word P0))))
              (sourceFunctionBody Guest.guestFn_trie_lookup)
            rw [bodyRun4] at meta4
            have r4c : r4.code = originalRuntimeCode := c4.trans (meta4.1.trans r3c)
            have r4mark : r4.locals.lookup (ofString "mark") = some (.val (.word P0)) := by
              rw [l4]
              have : ofString "r" ≠ ofString "mark" := by decide
              simp [HolFiniteMapExact.lookup_update,FUPDATE,this,r3loc,r2mark]
            have relArgs : evalListHOLFinite r4 (h := fun a => Classical.propDecidable (r4.memaddrs a))
                [.var .local (ofString "mark")] = some [.val (.word P0)] := by
              rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,r4mark]
            have relLookup := pan_single_word_lookup r4.code.lookup (ofString "heap_release") (ofString "m") _ P0
              (by rw [r4c]; exact vmLookup_heap_release)
            have hw := memWatch_discardCall r4 w _ _ _ relArgs _ _ _ relLookup
              (congrFun (heapRelease_body_memory _) w)
            rw [evaluateHOLFiniteState_seq_line780]
            cases r5run : evaluateHOLFiniteState r4 (.call (some (none,none)) (ofString "heap_release")
                [.var .local (ofString "mark")]) with
            | mk res5 r5 =>
              rw [r5run] at hw
              have chain : r4.memory w = r3.memory w := by rw [m4]; exact W
              cases res5 with
              | some x => exact hw.trans chain
              | none =>
                dsimp only
                rw [congrFun (evaluate_readOnly_memory (.return (.var .local (ofString "r"))) (by decide) r5) w]
                exact hw.trans chain

#print axioms wsAccountLeaf_body_window
end InitECandidate.Runtime
