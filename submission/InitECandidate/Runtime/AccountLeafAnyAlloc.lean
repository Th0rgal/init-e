import InitECandidate.Runtime.AccountLeafWindow
import InitECandidate.Runtime.TrapCallTerminal
import InitECandidate.Runtime.HtabGrowRehash
import InitECandidate.Runtime.HtabGrowTop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Programs that keep the whole memory in every outcome under the original code. -/
def MemKeep (program : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
    (evaluateHOLFiniteState s program).2.memory = s.memory

theorem memKeep_leaf (p : ProgHOL 64) (ro : readOnlyMemory p = true) : MemKeep p :=
  fun s _ => evaluate_readOnly_memory p ro s

theorem memKeep_assign (k : VarKind) (n : MlS) (e : ExpHOL 64) : MemKeep (.assign k n e) :=
  fun s _ => evaluate_assign_memory s k n e

theorem memKeep_seq {p q : ProgHOL 64} (hp : MemKeep p) (hq : MemKeep q) : MemKeep (.seq p q) := by
  intro F s code
  have h1 := hp s code
  have meta' := evaluateHOLFiniteState_metadata s p
  rw [evaluateHOLFiniteState_seq_line780]
  cases r : evaluateHOLFiniteState s p with
  | mk res m =>
    rw [r] at h1 meta'
    cases res with
    | some x => exact h1
    | none => exact (hq m (meta'.1.trans code)).trans h1

theorem memKeep_dec (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64} (hb : MemKeep body) :
    MemKeep (.dec name shape init body) := by
  intro F s code
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · rfl
  · split
    · exact hb _ (by exact code)
    · rfl

theorem memKeep_ite (c : ExpHOL 64) {y n : ProgHOL 64} (hy : MemKeep y) (hn : MemKeep n) : MemKeep (.ite c y n) := by
  intro F s code
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact hn s code
    · exact hy s code
  · rfl

theorem shMemStore_exact_memory {F : Type} (st : PanSemStateExact 64 F) [DecidablePred st.shMemaddrs]
    (word address : BitVec 64) (nb : Nat) : (shMemStoreHOLExact st word address nb).2.memory = st.memory := by
  unfold shMemStoreHOLExact
  split
  · split
    · split <;> rfl
    · rfl
  · split
    · split <;> rfl
    · rfl

theorem memKeep_shMemStore (op : OpSize) (a v : ExpHOL 64) : MemKeep (.shMemStore op a v) := by
  intro F s _
  rw [evaluateHOLFiniteState_shMemStore_total]
  dsimp only
  split
  · exact @shMemStore_exact_memory _ _ (fun k => Classical.propDecidable _) _ _ _
  · rfl

theorem memKeep_extCall_zero (f : MlS) (a b c : ExpHOL 64) : MemKeep (.extCall f a b c (.const 0)) := by
  intro F s _
  rw [evaluateHOLFiniteState_extCall_source]
  have e0 : evalHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x)) (.const 0) =
      some (.val (.word 0)) := by rw [evalHOLFinite_eq_toExact]; rfl
  rw [e0]
  split
  · split
    · rename_i hl _ _ _ b2 _ hb2
      simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at hl
      subst hl
      have len := readBytearrayWordHOL_length _ _ _ b2 hb2
      split
      · rfl
      · rename_i newFfi newBytes hret
        have nl := callFFIHOL_ret_length _ _ _ _ _ _ hret
        have : newBytes = [] := by
          apply List.eq_nil_of_length_eq_zero; rw [nl,len]; rfl
        subst this
        rfl
    · rfl
  · rfl

theorem memKeep_discardCall (function : MlS) (arguments : List (ExpHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (bodyKeep : MemKeep body) : MemKeep (.call (some (none,none)) function arguments) := by
  intro F state code
  rw [evaluateHOLFiniteState_call]
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => simp
  | some values =>
    dsimp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => simp
    | some data =>
      obtain ⟨found,callee,foundShape⟩ := data
      dsimp only
      have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body found returnShape
        foundShape values callee (by rw [code]; exact installed) lookup
      subst same
      split
      · simp [emptyLocalsHOLFinite]
      · have frame := bodyKeep (callEntryStateHOLFinite state callee) code
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at frame
          change bodyPost.memory = state.memory at frame
          rcases rb with _ | (_ | _ | _ | _ | w | _ | _)
          all_goals (dsimp only; try split)
          all_goals exact frame

theorem trapWith_memKeep : MemKeep (sourceFunctionBody Guest.guestFn_trap_with) := by
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  repeat first
    | exact memKeep_leaf _ (by decide)
    | apply memKeep_seq
    | exact memKeep_shMemStore _ _ _
    | exact memKeep_extCall_zero _ _ _ _

theorem alloc_memKeep : MemKeep (sourceFunctionBody Guest.guestFn_alloc) := by
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  repeat first
    | exact memKeep_leaf _ (by decide)
    | apply memKeep_seq
    | apply memKeep_dec
    | apply memKeep_ite
    | exact memKeep_assign _ _ _
    | exact memKeep_discardCall _ _ _ _ _ originalRuntimeCode_trap_lookup trapWith_memKeep

#print axioms trapWith_memKeep
#print axioms alloc_memKeep

set_option maxHeartbeats 8000000 in
/-- The original `ws_account_leaf(addr)` keeps every word outside the Keccak state and pad, the 32-byte hash block
it allocates at the entry heap pointer, and the nibble scratch buffer, in every outcome (including `MptErr` from
the trie walk and the allocator trap `TrapErr` when the block does not fit); no space premise. -/
theorem wsAccountLeaf_body_window_any {F : Type} (s : PanSemStateFiniteExact 64 F) (A P0 K Pd NB w : BitVec 64)
    (code : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "addr") = some (.val (.word A)))
    (hheap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word P0)))
    (hK : s.globals.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd : s.globals.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB : s.globals.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
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
    apply decCall_watch
    · intro values body callee rs hargs hl
      rw [allocArgs values hargs,allocLookup] at hl
      simp only [Option.some.injEq,Prod.mk.injEq] at hl
      obtain ⟨rfl,rfl,rfl⟩ := hl
      exact congrFun (alloc_memKeep _ (by exact rc)) w
    · intro values body callee rs v2 post2' hargs hl bodyRun2 r2 m2 g2 c2 a2 b2 l2
      rw [allocArgs values hargs,allocLookup] at hl
      simp only [Option.some.injEq,Prod.mk.injEq] at hl
      obtain ⟨rfl,rfl,rfl⟩ := hl
      obtain ⟨_,_,rfl,mem2,addr2,_,code2,glob2⟩ := alloc_body_returned _ post2' P0 32 (by exact rc) E2heap E2n v2 bodyRun2
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

#print axioms wsAccountLeaf_body_window_any

theorem discard_normal_full {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (run : evaluateHOLFiniteState state (.call (some (none,none)) function arguments) = (none,post)) :
    ∃ value output, evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (some (.returned value),output) ∧
      post.memory = output.memory ∧ post.locals = state.locals ∧ post.globals = output.globals := by
  rw [evaluateHOLFiniteState_call,args] at run
  simp only at run
  rw [lookup] at run
  simp only at run
  split at run
  · cases run
  · cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
    | mk result output =>
      rw [bodyRun] at run
      cases result with
      | none => cases run
      | some result =>
        cases result with
        | returned value =>
          simp only at run
          split at run
          · refine ⟨value,output,rfl,?_,?_,?_⟩
            all_goals rw [← (Prod.mk.inj run).2]
          · cases run
        | error => cases run
        | timeOut => cases run
        | «break» => cases run
        | «continue» => cases run
        | finalFfi ffi => cases run
        | exception exceptionId value => cases run

theorem seq_discard_returned {F : Type} {s post : PanSemStateFiniteExact 64 F} {f : MlS} {args : List (ExpHOL 64)}
    {b : ProgHOL 64} {v : ValueHOL 64}
    (run : evaluateHOLFiniteState s (.seq (.call (some (none,none)) f args) b) = (some (.returned v),post)) :
    ∃ mid, evaluateHOLFiniteState s (.call (some (none,none)) f args) = (none,mid) ∧
      evaluateHOLFiniteState mid b = (some (.returned v),post) := by
  have nr := discard_call_not_returned s f args v
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases h : evaluateHOLFiniteState s (.call (some (none,none)) f args) with
  | mk r m =>
    rw [h] at run nr
    cases r with
    | none => exact ⟨m,rfl,run⟩
    | some x =>
      obtain ⟨e,_⟩ := Prod.mk.inj run
      simp only [Option.some.injEq] at e
      subst e
      exact absurd rfl nr

theorem trieLookup_globalsFrame : OriginalGlobalsFrame (sourceFunctionBody Guest.guestFn_trie_lookup) := by
  rw [source_trieLookup_body]
  unfold trieLookupBody
  apply originalGlobalsFrame_sequence
  · exact originalGlobalsFrame_discard_call _ _ _ _ originalRuntimeCode_keyToNibbles_lookup
      (originalGlobalsFrame_leaf _ (fun _ => by
        simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]; rfl)) _
  · intro F s code
    exact (memoryFrame_tailCall _ _ _ _ _ originalRuntimeCode_trieWalk_lookup trieWalk_memoryFrame s code).2

#print axioms trieLookup_globalsFrame

theorem discard_normal_any {F : Type} (state post : PanSemStateFiniteExact 64 F) (function : MlS)
    (arguments : List (ExpHOL 64))
    (run : evaluateHOLFiniteState state (.call (some (none,none)) function arguments) = (none,post)) :
    ∃ values body callee rs value output,
      evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments = some values ∧
      lookupCodeHOLFinite state.code.lookup function values = some (body,callee,rs) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (some (.returned value),output) ∧
      post.memory = output.memory ∧ post.locals = state.locals ∧ post.globals = output.globals := by
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none =>
    rw [evaluateHOLFiniteState_call,args] at run; simp at run
  | some values =>
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none =>
      rw [evaluateHOLFiniteState_call,args] at run; simp only at run; rw [lookup] at run; simp at run
    | some data =>
      obtain ⟨body,callee,rs⟩ := data
      obtain ⟨value,output,br,m,l,g⟩ := discard_normal_full state post function arguments values body callee rs args lookup run
      exact ⟨values,body,callee,rs,value,output,rfl,lookup,br,m,l,g⟩

set_option maxHeartbeats 8000000 in
/-- Normal return of the original `ws_account_leaf`: `heap_release(mark)` restores the heap pointer, so every
global (including `heap_ptr`) is as at entry. (On `MptErr`, `TrapErr` or other non-normal exits there is no
restoration guarantee for the heap pointer; only the memory window `wsAccountLeaf_body_window_any` holds.) -/
theorem wsAccountLeaf_returned_globals {F : Type} (s post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (P0 : BitVec 64) (code : s.code = originalRuntimeCode)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word P0)))
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_ws_account_leaf) = (some (.returned v),post)) :
    ∀ name, post.globals.lookup name = s.globals.lookup name := by
  rw [source_wsAccountLeaf_hol] at run
  unfold wsAccountLeafHOL at run
  obtain ⟨vals1,b1,c1,rs1,w1,bp1,res1,in1,a1,l1,br1,_,_,_,rc1,rg1,_,rmark1,rloc1,cr1,_,_,_,_,pg1⟩ :=
    decCall_returned_globalsG run
  have v1 : vals1 = [] := by rw [evalListHOLFinite_eq_toExact] at a1; simp [evalListHOLExact] at a1; exact a1
  subst v1
  rw [pan_no_args_lookup s.code.lookup (ofString "heap_mark") _ (by rw [code]; exact vmLookup_heap_mark)] at l1
  simp only [Option.some.injEq,Prod.mk.injEq] at l1
  obtain ⟨rfl,rfl,rfl⟩ := l1
  rw [source_heapMark_body,evaluateHOLFiniteState_return] at br1
  have e : @evalHOLExact 64 F _ (callEntryStateHOLFinite s HolFiniteMapExact.empty).toExact
      (fun a => Classical.propDecidable ((callEntryStateHOLFinite s HolFiniteMapExact.empty).memaddrs a))
      (.var .global (ofString "heap_ptr")) = some (.val (.word P0)) := by
    simp [evalHOLExact,callEntryStateHOLFinite,heap]
  rw [e] at br1
  simp [shapeOfHOLExact] at br1
  obtain ⟨rfl,rfl⟩ := br1
  have g1 : res1.globals = s.globals := rg1
  have c1' : res1.code = originalRuntimeCode := rc1.trans code
  -- alloc
  obtain ⟨vals2,b2,c2,rs2,w2,bp2,res2,in2,a2,l2,br2,_,_,_,rc2,rg2,_,rh2,rloc2,cr2,_,_,_,_,pg2⟩ :=
    decCall_returned_globalsG cr1
  have v2 : vals2 = [.val (.word 32)] := by
    rw [evalListHOLFinite_eq_toExact] at a2; simp [evalListHOLExact,evalHOLExact] at a2; exact a2.symm
  subst v2
  rw [pan_single_word_lookup res1.code.lookup (ofString "alloc") (ofString "n") _ 32
    (by rw [c1']; exact originalRuntimeCode_allocation_lookup)] at l2
  simp only [Option.some.injEq,Prod.mk.injEq] at l2
  obtain ⟨rfl,rfl,rfl⟩ := l2
  obtain ⟨_,_,rfl,_,_,_,bc2,bg2⟩ := alloc_body_returned _ bp2 P0 32 (by exact c1')
    (by change res1.globals.lookup _ = _; rw [g1]; exact heap)
    (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) w2 br2
  have c2' : res2.code = originalRuntimeCode := rc2.trans (bc2.trans c1')
  have mark2 : res2.locals.lookup (ofString "mark") = some (.val (.word P0)) := by
    rw [rloc2 _ (by decide)]; exact rmark1
  -- keccak call
  obtain ⟨mid3,k3,cr3⟩ := seq_discard_returned cr2
  have g3 : mid3.globals = res2.globals := by
    have := keccak_call_globals_frame [.var .local (ofString "addr"),.const 20,.var .local (ofString "h")] res2 c2'
    rw [k3] at this; exact this
  have meta3 := evaluateHOLFiniteState_metadata res2 (.call (some (none,none)) (ofString "keccak256")
    [.var .local (ofString "addr"),.const 20,.var .local (ofString "h")])
  rw [k3] at meta3
  have c3 : mid3.code = originalRuntimeCode := meta3.1.trans c2'
  obtain ⟨_,_,_,_,_,_,_,_,_,_,l3,_⟩ := discard_normal_any res2 mid3 _ _ k3
  -- trie_lookup
  obtain ⟨vals4,b4,c4,rs4,w4,bp4,res4,in4,a4,lk4,br4,_,_,_,rc4,rg4,_,_,rloc4,cr4,_,_,_,_,pg4⟩ :=
    decCall_returned_globalsG cr3
  have body4 := lookupCodeHOLFinite_installed_body mid3.code.lookup (ofString "trie_lookup") _ _ b4 _ rs4 vals4 c4
    (by rw [c3]; exact originalRuntimeCode_trieLookup_lookup) lk4
  subst body4
  have g4 : bp4.globals = mid3.globals := by
    have := trieLookup_globalsFrame (callEntryStateHOLFinite mid3 c4) (by exact c3)
    rw [br4] at this; exact this
  have meta4 := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite mid3 c4) (sourceFunctionBody Guest.guestFn_trie_lookup)
  rw [br4] at meta4
  have c4' : res4.code = originalRuntimeCode := rc4.trans (meta4.1.trans c3)
  have mark4 : res4.locals.lookup (ofString "mark") = some (.val (.word P0)) := by
    rw [rloc4 _ (by decide),l3]; exact mark2
  -- heap_release then return
  obtain ⟨mid5,k5,cr5⟩ := seq_discard_returned cr4
  obtain ⟨vals5,b5,c5,rs5,w5,out5,a5,lk5,br5,_,_,g5⟩ := discard_normal_any res4 mid5 _ _ k5
  have v5 : vals5 = [.val (.word P0)] := by
    rw [evalListHOLFinite_eq_toExact] at a5; simp [evalListHOLExact,evalHOLExact,mark4] at a5; exact a5.symm
  subst v5
  rw [pan_single_word_lookup res4.code.lookup (ofString "heap_release") (ofString "m") _ P0
    (by rw [c4']; exact vmLookup_heap_release)] at lk5
  simp only [Option.some.injEq,Prod.mk.injEq] at lk5
  obtain ⟨rfl,rfl,rfl⟩ := lk5
  -- globals along the path
  have G4 : res4.globals = (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word (allocationEnd P0 32)))
      (callEntryStateHOLFinite res1 (HolFiniteMapExact.empty.update (ofString "n",.val (.word 32))))).globals := by
    rw [rg4,g4,g3,rg2,bg2]
  generalize hE5 : callEntryStateHOLFinite res4 (HolFiniteMapExact.empty.update (ofString "m",.val (.word P0))) = E5 at br5
  have E5m : E5.locals.lookup (ofString "m") = some (.val (.word P0)) := by
    rw [← hE5]; simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have E5g : E5.globals = res4.globals := by rw [← hE5]; rfl
  have E5h : E5.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd P0 32))) := by
    rw [E5g,G4]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have hAs : evaluateHOLFiniteState E5 (.assign .global (ofString "heap_ptr") (.var .local (ofString "m"))) =
      (none,setGlobalHOLFinite (ofString "heap_ptr") (.val (.word P0)) E5) := by
    simp [evaluateHOLFiniteState_assign,evalHOLExact,isValidValueHOLExact,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite,
      lookupKvarHOLExact,E5m,E5h]
  rw [source_heapRelease_body,evaluateHOLFiniteState_seq_line780,hAs] at br5
  dsimp only at br5
  rw [evaluateHOLFiniteState_return] at br5
  simp [evalHOLExact,shapeOfHOLExact] at br5
  obtain ⟨_,rfl⟩ := br5
  rw [evaluateHOLFiniteState_return] at cr5
  split at cr5
  · simp at cr5
  · split at cr5
    · obtain ⟨_,rfl⟩ := Prod.mk.inj cr5
      intro name
      rw [pg1,pg2,pg4]
      change mid5.globals.lookup name = _
      rw [g5]
      change (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word P0)) E5).globals.lookup name = _
      by_cases hn : name = ofString "heap_ptr"
      · subst hn; rw [heap]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      · rw [show (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word P0)) E5).globals.lookup name = E5.globals.lookup name by
          simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm hn]]
        rw [E5g,G4]
        simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm hn,callEntryStateHOLFinite,g1]
    · simp at cr5

#print axioms wsAccountLeaf_returned_globals
end InitECandidate.Runtime
