import InitECandidate.Runtime.HtabSetBound
import InitECandidate.Runtime.GlobalsFrameComposition
import InitECandidate.Runtime.DiscardCallGlobalsFrame
import InitECandidate.Runtime.HeapGlobalsFrame
import InitECandidate.Runtime.MemcpyGlobals
import InitECandidate.Runtime.OriginalMemcpyCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An outcome that does not abort: normal completion, loop control, or a return. -/
def Continuing (r : Option (PanSemResultExact 64)) : Prop :=
  r = none ∨ r = some .continue ∨ r = some .break ∨ ∃ v, r = some (.returned v)

/-- A reflexive, transitive relation on global maps. -/
structure GlobalsPreorder (R : HolFiniteMapExact MlS (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64) → Prop) : Prop where
  refl : ∀ g, R g g
  trans : ∀ a b c, R a b → R b c → R a c

/-- On every continuing outcome under the original code, the globals before and after are related. -/
@[irreducible] def NormalRel (R : HolFiniteMapExact MlS (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (program : ProgHOL 64) : Prop :=
  ∀ {F : Type} (state post : PanSemStateFiniteExact 64 F) (r : Option (PanSemResultExact 64)),
    state.code = originalRuntimeCode → evaluateHOLFiniteState state program = (r,post) → Continuing r →
      R state.globals post.globals

/-- On every returned outcome under the original code, the globals are related. -/
@[irreducible] def ReturnedRel (R : HolFiniteMapExact MlS (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (program : ProgHOL 64) : Prop :=
  ∀ {F : Type} (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
    state.code = originalRuntimeCode → evaluateHOLFiniteState state program = (some (.returned v),post) →
      R state.globals post.globals

theorem NormalRel.returned {R} {program : ProgHOL 64} (rel : NormalRel R program) : ReturnedRel R program := by
  unfold NormalRel at rel; unfold ReturnedRel
  exact fun state post v code run => rel state post _ code run (Or.inr (Or.inr (Or.inr ⟨v,rfl⟩)))

theorem normalRel_of_frame {R} (pre : GlobalsPreorder R) {program : ProgHOL 64} (frame : OriginalGlobalsFrame program) :
    NormalRel R program := by
  unfold NormalRel
  intro F state post r code run _
  have same := frame state code
  rw [run] at same
  change post.globals = state.globals at same
  rw [same]; exact pre.refl _

theorem normalRel_readOnly {R} (pre : GlobalsPreorder R) {program : ProgHOL 64} (supported : readOnlyMemory program = true) :
    NormalRel R program := by
  unfold NormalRel
  intro F state post r _ run _
  have same := evaluate_readOnly_globals program supported state
  rw [run] at same
  change post.globals = state.globals at same
  rw [same]; exact pre.refl _

theorem normalRel_seq {R} (pre : GlobalsPreorder R) {first second : ProgHOL 64} (a : NormalRel R first)
    (b : NormalRel R second) : NormalRel R (.seq first second) := by
  unfold NormalRel at *
  intro F state post r code run cont
  have metadata := evaluateHOLFiniteState_metadata state first
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases firstRun : evaluateHOLFiniteState state first with
  | mk r1 mid =>
    rw [firstRun] at run metadata
    cases r1 with
    | none =>
      simp only at run
      exact pre.trans _ _ _ (a state mid none code firstRun (Or.inl rfl)) (b mid post r (metadata.1.trans code) run cont)
    | some r1 =>
      obtain ⟨e,rfl⟩ := Prod.mk.inj run
      subst e
      exact a state mid _ code firstRun cont

theorem normalRel_dec {R} (pre : GlobalsPreorder R) (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64)
    {body : ProgHOL 64} (frame : NormalRel R body) : NormalRel R (.dec name shape initializer body) := by
  unfold NormalRel at *
  intro F state post r code run cont
  rw [evaluateHOLFiniteState_dec_total] at run
  dsimp only at run
  split at run
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj run
    rcases cont with h | h | h | ⟨v,h⟩ <;> cases h
  · rename_i value _
    split at run
    · cases inner : evaluateHOLFiniteState (setVarHOLFinite name value state) body with
      | mk ir ip =>
        rw [inner] at run
        obtain ⟨e,p⟩ := Prod.mk.inj run
        subst p
        simp only at e
        subst e
        exact frame (setVarHOLFinite name value state) ip ir (by exact code) inner cont
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj run
      rcases cont with h | h | h | ⟨v,h⟩ <;> cases h

theorem normalRel_ite {R} (_pre : GlobalsPreorder R) (condition : ExpHOL 64) {yes no : ProgHOL 64}
    (a : NormalRel R yes) (b : NormalRel R no) : NormalRel R (.ite condition yes no) := by
  unfold NormalRel at *
  intro F state post r code run cont
  rw [evaluateHOLFiniteState_ite] at run
  split at run
  · split at run
    · exact b state post r code run cont
    · exact a state post r code run cont
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj run
    rcases cont with h | h | h | ⟨v,h⟩ <;> cases h

#print axioms normalRel_dec

theorem normalRel_apply {R} {program : ProgHOL 64} (rel : NormalRel R program) {F : Type}
    {X : PanSemStateFiniteExact 64 F} (cont : Continuing (evaluateHOLFiniteState X program).1)
    (code : X.code = originalRuntimeCode) : R X.globals (evaluateHOLFiniteState X program).2.globals := by
  unfold NormalRel at rel
  exact rel X _ _ code rfl cont

theorem normalRel_while {R} (pre : GlobalsPreorder R) (condition : ExpHOL 64) {body : ProgHOL 64}
    (frame : NormalRel R body) : NormalRel R (.while condition body) := by
  unfold NormalRel at *
  intro F state post r code run cont
  have main : ∀ n : Nat, ∀ (s q : PanSemStateFiniteExact 64 F) (rr : Option (PanSemResultExact 64)), s.clock = n →
      s.code = originalRuntimeCode → evaluateHOLFiniteState s (.while condition body) = (rr,q) → Continuing rr →
      R s.globals q.globals := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro s q rr clock scode srun scont
      rw [evaluateHOLFiniteState_while_total] at srun
      split at srun
      · split at srun
        · split at srun
          · obtain ⟨rfl,rfl⟩ := Prod.mk.inj srun
            rcases scont with h | h | h | ⟨v,h⟩ <;> cases h
          · dsimp only at srun
            rw [fixClockHOLFinite_evaluateState] at srun
            have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
            have metadata := evaluateHOLFiniteState_metadata (decClockHOLFinite s) body
            cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite s) body with
            | mk rb mid =>
              rw [bodyRun] at srun remaining metadata
              have smaller : mid.clock < n := by
                change mid.clock ≤ s.clock - 1 at remaining
                omega
              have step := fun (h : Continuing rb) => frame (decClockHOLFinite s) mid rb (by exact scode) bodyRun h
              cases rb with
              | none =>
                exact pre.trans _ _ _ (step (Or.inl rfl))
                  (ih mid.clock (by omega) mid q rr rfl (metadata.1.trans scode) srun scont)
              | some rb =>
                cases rb with
                | «continue» =>
                  exact pre.trans _ _ _ (step (Or.inr (Or.inl rfl)))
                    (ih mid.clock (by omega) mid q rr rfl (metadata.1.trans scode) srun scont)
                | «break» =>
                  obtain ⟨_,rfl⟩ := Prod.mk.inj srun
                  exact step (Or.inr (Or.inr (Or.inl rfl)))
                | returned w =>
                  obtain ⟨_,rfl⟩ := Prod.mk.inj srun
                  exact step (Or.inr (Or.inr (Or.inr ⟨w,rfl⟩)))
                | _ =>
                  obtain ⟨e,rfl⟩ := Prod.mk.inj srun
                  subst e
                  rcases scont with h | h | h | ⟨v,h⟩ <;> cases h
        · obtain ⟨_,rfl⟩ := Prod.mk.inj srun
          exact pre.refl _
      · obtain ⟨rfl,rfl⟩ := Prod.mk.inj srun
        rcases scont with h | h | h | ⟨v,h⟩ <;> cases h
  exact main state.clock state post r rfl code run cont

#print axioms normalRel_while

theorem normalRel_decCall {R} (pre : GlobalsPreorder R) (name function : MlS) (shape : ShapeHOL)
    (arguments : List (ExpHOL 64)) {continuation : ProgHOL 64} (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64)
    (returnShape : ShapeHOL) (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (bodyRel : ReturnedRel R body) (tailRel : NormalRel R continuation) :
    NormalRel R (.decCall name shape function arguments continuation) := by
  have tailRel' := tailRel
  unfold NormalRel at tailRel ⊢
  unfold ReturnedRel at bodyRel
  intro F state post r code run cont
  rw [evaluateHOLFiniteState_decCall_total] at run
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none =>
    rw [args] at run; simp only at run
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj run
    rcases cont with h | h | h | ⟨v,h⟩ <;> cases h
  | some values =>
    rw [args] at run
    dsimp only at run
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none =>
      rw [lookup] at run; simp only at run
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj run
      rcases cont with h | h | h | ⟨v,h⟩ <;> cases h
    | some data =>
      obtain ⟨found,callee,foundShape⟩ := data
      rw [lookup] at run
      dsimp only at run
      have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body found returnShape
        foundShape values callee (by rw [code]; exact installed) lookup
      subst same
      split at run
      · obtain ⟨rfl,rfl⟩ := Prod.mk.inj run
        rcases cont with h | h | h | ⟨v,h⟩ <;> cases h
      · have metadata := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) found
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at run metadata
          dsimp only [fixClockHOLFinite] at run
          rcases rb with _ | (_ | _ | _ | _ | w | _ | _)
          all_goals first
            | (obtain ⟨rfl,rfl⟩ := Prod.mk.inj run; rcases cont with h | h | h | ⟨v,h⟩ <;> cases h; done)
            | skip
          simp only [] at run
          split at run
          · have first := bodyRel (callEntryStateHOLFinite state callee) bodyPost w code bodyRun
            obtain ⟨e,rfl⟩ := Prod.mk.inj run
            subst e
            exact pre.trans _ _ _ first (normalRel_apply tailRel' cont (by exact metadata.1.trans code))
          · obtain ⟨rfl,rfl⟩ := Prod.mk.inj run
            rcases cont with h | h | h | ⟨v,h⟩ <;> cases h

#print axioms normalRel_decCall

theorem normalRel_discard_call {R} (pre : GlobalsPreorder R) (function : MlS) (arguments : List (ExpHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (bodyRel : ReturnedRel R body) : NormalRel R (.call (some (none,none)) function arguments) := by
  unfold NormalRel
  unfold ReturnedRel at bodyRel
  intro F state post r code run cont
  rw [evaluateHOLFiniteState_call] at run
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none =>
    rw [args] at run; simp only at run
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj run
    rcases cont with h | h | h | ⟨v,h⟩ <;> cases h
  | some values =>
    rw [args] at run
    dsimp only at run
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none =>
      rw [lookup] at run; simp only at run
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj run
      rcases cont with h | h | h | ⟨v,h⟩ <;> cases h
    | some data =>
      obtain ⟨found,callee,foundShape⟩ := data
      rw [lookup] at run
      dsimp only at run
      have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body found returnShape
        foundShape values callee (by rw [code]; exact installed) lookup
      subst same
      split at run
      · obtain ⟨rfl,rfl⟩ := Prod.mk.inj run
        rcases cont with h | h | h | ⟨v,h⟩ <;> cases h
      · cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at run
          rcases rb with _ | (_ | _ | _ | _ | w | _ | _)
          all_goals first
            | (simp only at run; obtain ⟨rfl,rfl⟩ := Prod.mk.inj run; rcases cont with h | h | h | ⟨v,h⟩ <;> cases h; done)
            | skip
          all_goals first
            | (simp only at run; split at run
               all_goals (obtain ⟨rfl,rfl⟩ := Prod.mk.inj run)
               all_goals first
                 | exact bodyRel (callEntryStateHOLFinite state callee) bodyPost w code bodyRun
                 | (rcases cont with h | h | h | ⟨v,h⟩ <;> cases h))
            | skip

#print axioms normalRel_discard_call

/-- Non-heap globals are kept, and an aligned in-arena heap word stays an
aligned in-arena word that does not decrease. -/
def HeapRel (before after : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  (∀ name, name ≠ ofString "heap_ptr" → after.lookup name = before.lookup name) ∧
  ∀ p0 : BitVec 64, before.lookup (ofString "heap_ptr") = some (.val (.word p0)) → p0.toNat % 8 = 0 →
    p0.toNat ≤ 33806089496 →
    ∃ p1 : BitVec 64, after.lookup (ofString "heap_ptr") = some (.val (.word p1)) ∧ p0.toNat ≤ p1.toNat ∧
      p1.toNat % 8 = 0 ∧ p1.toNat ≤ 33806089496

theorem heapRel_preorder : GlobalsPreorder HeapRel where
  refl := fun g => ⟨fun _ _ => rfl,fun p0 h a b => ⟨p0,h,le_refl _,a,b⟩⟩
  trans := by
    intro a b c ab bc
    refine ⟨fun name ne => (bc.1 name ne).trans (ab.1 name ne),fun p0 h al le => ?_⟩
    obtain ⟨p1,h1,l1,a1,b1⟩ := ab.2 p0 h al le
    obtain ⟨p2,h2,l2,a2,b2⟩ := bc.2 p1 h1 a1 b1
    exact ⟨p2,h2,by omega,a2,b2⟩

theorem discard_call_not_loopControl {F : Type} (state : PanSemStateFiniteExact 64 F) (function : MlS)
    (arguments : List (ExpHOL 64)) :
    (evaluateHOLFiniteState state (.call (some (none,none)) function arguments)).1 ≠ some .continue ∧
      (evaluateHOLFiniteState state (.call (some (none,none)) function arguments)).1 ≠ some .break := by
  rw [evaluateHOLFiniteState_call]
  constructor <;> (repeat' first | split | (simp; done) | simp_all)

/-- A trap call never continues, whatever relation is tracked. -/
theorem normalRel_trap_call {R} (argument : ExpHOL 64) (value : BitVec 64)
    (args : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [argument] = some [.val (.word value)]) :
    NormalRel R (.call (some (none,none)) (ofString "trap_with") [argument]) := by
  unfold NormalRel
  intro F state post r code run cont
  have terminal := evaluate_trap_call_terminal state argument value code (args state)
  have notReturned := fun v => discard_call_not_returned state (ofString "trap_with") [argument] v
  have control := discard_call_not_loopControl state (ofString "trap_with") [argument]
  rw [run] at terminal notReturned control
  simp only at terminal notReturned control
  rcases cont with h | h | h | ⟨v,h⟩
  · exact absurd h terminal
  · exact absurd h control.1
  · exact absurd h control.2
  · exact absurd h (notReturned v)

#print axioms normalRel_trap_call

/-- A returned allocator body read a word heap pointer and a word size. -/
theorem alloc_returned_words {F : Type} (state post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_alloc) = (some (.returned v),post)) :
    ∃ pointer size : BitVec 64, state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)) ∧
      state.locals.lookup (ofString "n") = some (.val (.word size)) := by
  rw [source_alloc_body] at run
  obtain ⟨pv,_,e1,r1,_,_,_,_⟩ := dec_returned_state run
  have heapEval : state.globals.lookup (ofString "heap_ptr") = some pv := by
    simp [evalHOLExact] at e1; exact e1
  unfold allocationAfterPointer at r1
  rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite] at r1
  have nL : (setVarHOLFinite (ofString "p") pv state).locals.lookup (ofString "n") = state.locals.lookup (ofString "n") := by
    simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have pL : (setVarHOLFinite (ofString "p") pv state).locals.lookup (ofString "p") = some pv := by
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  cases pv with
  | val pw =>
    cases pw with
    | word pointer =>
      cases nCase : state.locals.lookup (ofString "n") with
      | none =>
        rw [nCase] at nL
        simp [allocationRequestCheck,evalHOLExact,evalListHOLExact,pL,nL,wordOpHOL,wordOp,valueIsWord,valueWord] at r1
      | some nv =>
        cases nv with
        | val nw =>
          cases nw with
          | word size => exact ⟨pointer,size,heapEval,rfl⟩
        | _ =>
          rw [nCase] at nL
          simp [allocationRequestCheck,evalHOLExact,evalListHOLExact,pL,nL,wordOpHOL,wordOp,valueIsWord,valueWord] at r1
  | _ =>
    simp [allocationRequestCheck,evalHOLExact,evalListHOLExact,pL,nL,wordOpHOL,wordOp,valueIsWord,valueWord] at r1

#print axioms alloc_returned_words

theorem alloc_returnedRel : ReturnedRel HeapRel (sourceFunctionBody Guest.guestFn_alloc) := by
  unfold ReturnedRel
  intro F state post v code run
  obtain ⟨pointer,size,heap,sizeL⟩ := alloc_returned_words state post v run
  obtain ⟨request,finish,_,_,_,_,_,globals⟩ := alloc_body_returned state post pointer size code heap sizeL v run
  have sub : ((33806089496 : BitVec 64) - pointer).toNat = 33806089496 - pointer.toNat ∨ 33806089496 < pointer.toNat := by
    by_cases le : pointer.toNat ≤ 33806089496
    · left; rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change pointer.toNat ≤ 33806089496; exact le))]; rfl
    · right; omega
  refine ⟨fun name ne => ?_,fun p0 h aligned inside => ?_⟩
  · rw [globals]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne]
  · rw [heap] at h
    simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at h
    subst h
    obtain ⟨cov,align,_⟩ := alloc_step_layout pointer size inside request
    refine ⟨allocationEnd pointer size,?_,by omega,align,finish⟩
    rw [globals]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms alloc_returnedRel

theorem heapRel_leaf {program : ProgHOL 64} (supported : ∀ watched, avoidsGlobalAssignment watched program = true) :
    NormalRel HeapRel program :=
  normalRel_of_frame heapRel_preorder (originalGlobalsFrame_leaf program supported)

theorem memcpy_returnedRel : ReturnedRel HeapRel (sourceFunctionBody Guest.guestFn_memcpy) :=
  NormalRel.returned (normalRel_of_frame heapRel_preorder (fun state _ => evaluate_memcpy_body_globals state))

/-- The original insertion keeps every global on continuing outcomes. -/
theorem htabInsertRaw_normalRel : NormalRel HeapRel (sourceFunctionBody Guest.guestFn_htab_insert_raw) := by
  have pre := heapRel_preorder
  rw [source_htabInsertRaw_body]
  repeat apply normalRel_dec pre
  apply normalRel_decCall pre _ _ _ _ _ _ _ originalRuntimeCode_hash_lookup
    (NormalRel.returned (normalRel_readOnly pre htabHash_readOnly))
  apply normalRel_dec pre
  apply normalRel_seq pre (normalRel_while pre _ (heapRel_leaf (fun _ => rfl)))
  apply normalRel_seq pre _ (heapRel_leaf (fun _ => rfl))
  exact normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_memcpy_lookup memcpy_returnedRel

#print axioms htabInsertRaw_normalRel

theorem memzero_returnedRel : ReturnedRel HeapRel (sourceFunctionBody Guest.guestFn_memzero) :=
  NormalRel.returned (heapRel_leaf (fun _ => by rw [source_memzero_body]; rfl))

theorem rehashBody_normalRel : NormalRel HeapRel hashGrowRehashBody := by
  have pre := heapRel_preorder
  unfold hashGrowRehashBody
  apply normalRel_dec pre
  apply normalRel_seq pre _ (heapRel_leaf (fun _ => rfl))
  exact normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_hashInsert_lookup (NormalRel.returned htabInsertRaw_normalRel)

/-- The original growth keeps every non-heap global and moves an aligned
in-arena heap word only upward inside the arena, on continuing outcomes. -/
theorem htabGrow_normalRel : NormalRel HeapRel (sourceFunctionBody Guest.guestFn_htab_grow) := by
  have pre := heapRel_preorder
  rw [source_htabGrow_body]
  repeat apply normalRel_dec pre
  unfold htabGrowAllocs
  repeat apply normalRel_decCall pre _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup alloc_returnedRel
  apply normalRel_seq pre (normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_memzero_lookup memzero_returnedRel)
  unfold htabGrowHeaderStores
  repeat apply normalRel_seq pre (heapRel_leaf (fun _ => rfl))
  apply normalRel_dec pre
  exact normalRel_seq pre (normalRel_while pre _ rehashBody_normalRel) (heapRel_leaf (fun _ => rfl))

/-- The original set keeps every non-heap global and moves an aligned in-arena
heap word only upward inside the arena, on continuing outcomes. -/
theorem htabSet_normalRel : NormalRel HeapRel (sourceFunctionBody Guest.guestFn_htab_set) := by
  have pre := heapRel_preorder
  rw [source_htabSet_body]
  have findRel : ReturnedRel HeapRel (sourceFunctionBody Guest.guestFn_htab_find_slot) := by
    apply NormalRel.returned
    apply normalRel_of_frame pre
    intro F state code
    exact (htabFindSlot_memoryFrame state code).2
  apply normalRel_decCall pre _ _ _ _ _ _ _ originalRuntimeCode_hashFind_lookup findRel
  apply normalRel_seq pre (heapRel_leaf (fun _ => rfl))
  apply normalRel_seq pre (normalRel_ite pre _
    (normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_hashGrow_lookup (NormalRel.returned htabGrow_normalRel))
    (heapRel_leaf (fun _ => rfl)))
  exact normalRel_seq pre (normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_hashInsert_lookup
    (NormalRel.returned htabInsertRaw_normalRel)) (heapRel_leaf (fun _ => rfl))

#print axioms htabGrow_normalRel
#print axioms htabSet_normalRel
end InitECandidate.Runtime
