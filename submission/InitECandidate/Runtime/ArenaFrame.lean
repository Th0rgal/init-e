import InitECandidate.Runtime.AccountLeafAnyAlloc
import InitECandidate.Runtime.RlpReadFrame
import InitECandidate.Runtime.ScratchAllocationSuccess
import InitECandidate.Runtime.OriginalScratchAllocationCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned run through a trap guard `if c { trap_with(k) }` took the skip branch with `c = 0`. -/
theorem trapIte_seq_returned {F : Type} (s : PanSemStateFiniteExact 64 F) (c : ExpHOL 64) (k : BitVec 64)
    (rest : ProgHOL 64) (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F) (code : s.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState s (.seq (.ite c (.call (some (none,none)) (ofString "trap_with") [.const k]) .skip) rest) =
      (some (.returned v),post)) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) c = some (.val (.word 0)) ∧
      evaluateHOLFiniteState s rest = (some (.returned v),post) := by
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.const k] =
      some [.val (.word k)] := by rw [evalListHOLFinite_eq_toExact]; rfl
  have term := evaluate_trap_call_terminal s (.const k) k code args
  have nr := discard_call_not_returned s (ofString "trap_with") [.const k] v
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases hI : evaluateHOLFiniteState s (.ite c (.call (some (none,none)) (ofString "trap_with") [.const k]) .skip) with
  | mk r m =>
    rw [hI] at run
    rw [evaluateHOLFiniteState_ite] at hI
    split at hI
    · rename_i w hw
      split at hI
      · rename_i hz
        subst hz
        rw [evaluateHOLFiniteState_skip] at hI
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj hI
        exact ⟨by rw [← evalHOLFinite_eq_toExact]; exact hw,run⟩
      · cases r with
        | none => rw [hI] at term; exact absurd rfl term
        | some x =>
          obtain ⟨e,_⟩ := Prod.mk.inj run
          simp only [Option.some.injEq] at e
          subst e
          rw [hI] at nr; exact absurd rfl nr
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj hI
      simp at run

#print axioms trapIte_seq_returned

/-- A normal return of the original `scratch_alloc(n)` (no clock or space premise): the request fitted above the
frame pointer, the rounded result `q` is at or above the frame pointer, it is returned and becomes `scratch_ptr`;
memory is unchanged. -/
theorem scratch_alloc_body_returned {F : Type} (E post : PanSemStateFiniteExact 64 F) (sp n FM : BitVec 64)
    (code : E.code = originalRuntimeCode)
    (hs : E.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp)))
    (hn : E.locals.lookup (ofString "n") = some (.val (.word n)))
    (hf : E.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word FM))) (w : ValueHOL 64)
    (run : evaluateHOLFiniteState E (sourceFunctionBody Guest.guestFn_scratch_alloc) = (some (.returned w),post)) :
    n ≤ sp - FM ∧ FM ≤ scratchAllocationEnd sp n ∧ w = .val (.word (scratchAllocationEnd sp n)) ∧
      post.memory = E.memory ∧ post.code = E.code ∧ post.memaddrs = E.memaddrs ∧ post.be = E.be ∧
      post.globals = (setGlobalHOLFinite (ofString "scratch_ptr") (.val (.word (scratchAllocationEnd sp n))) E).globals := by
  rw [source_scratch_alloc_body] at run
  obtain ⟨pv,inner1,e1,r1,m1,a1,b1,c1,g1⟩ := dec_returned_globals run
  have pE : @evalHOLExact 64 F _ E.toExact (fun a => Classical.propDecidable (E.memaddrs a))
      (.var .global (ofString "scratch_ptr")) = some (.val (.word sp)) := by simp [evalHOLExact,hs]
  rw [pE] at e1
  cases e1
  generalize hp : setVarHOLFinite (ofString "p") (.val (.word sp)) E = S1 at r1
  have pL : S1.locals.lookup (ofString "p") = some (.val (.word sp)) := by
    rw [← hp]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have nL : S1.locals.lookup (ofString "n") = some (.val (.word n)) := by
    rw [← hp]; simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hn]
  have fL : S1.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word FM)) := by rw [← hp]; exact hf
  have sL : S1.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp)) := by rw [← hp]; exact hs
  have S1c : S1.code = originalRuntimeCode := by rw [← hp]; exact code
  unfold scratchAllocationAfterPointer at r1
  obtain ⟨c0,r2⟩ := trapIte_seq_returned S1 _ 7 _ _ _ S1c r1
  have request : n ≤ sp - FM := by
    unfold scratchAllocationRequestCheck at c0
    simp [evalHOLExact,evalListHOLExact,pL,nL,fL,wordOpHOL,wordOp,valueIsWord,valueWord,
      Compiler.Encoders.Asm.wordCmpHOL] at c0
    exact BitVec.le_def.mpr (by omega)
  obtain ⟨qv,inner2,e2,r3,m2,a2,b2,c2,g2⟩ := dec_returned_globals r2
  rw [eval_scratchAllocationEndExpression S1 sp n pL nL] at e2
  cases e2
  generalize hq : setVarHOLFinite (ofString "q") (.val (.word (scratchAllocationEnd sp n))) S1 = S2 at r3
  have qL : S2.locals.lookup (ofString "q") = some (.val (.word (scratchAllocationEnd sp n))) := by
    rw [← hq]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have fL2 : S2.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word FM)) := by rw [← hq]; exact fL
  have sL2 : S2.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp)) := by rw [← hq]; exact sL
  have S2c : S2.code = originalRuntimeCode := by rw [← hq]; exact S1c
  have r3' := r3
  unfold scratchAllocationFinish at r3'
  obtain ⟨c1',_⟩ := trapIte_seq_returned S2 _ 7 _ _ _ S2c r3'
  have within : FM ≤ scratchAllocationEnd sp n := by
    simp [evalHOLExact,qL,fL2,Compiler.Encoders.Asm.wordCmpHOL] at c1'
    exact BitVec.le_def.mpr (by omega)
  rw [evaluate_scratchAllocationFinish S2 _ sp FM qL sL2 fL2 within] at r3
  obtain ⟨ew,rfl⟩ := Prod.mk.inj r3
  simp only [Option.some.injEq,PanSemResultExact.returned.injEq] at ew
  refine ⟨request,within,ew.symm,?_,?_,?_,?_,?_⟩
  · rw [m1,m2,← hq,← hp]; rfl
  · rw [c1,c2,← hq,← hp]; rfl
  · rw [a1,a2,← hq,← hp]; rfl
  · rw [b1,b2,← hq,← hp]; rfl
  · rw [g1,g2,← hq,← hp]; rfl

#print axioms scratch_alloc_body_returned

/-- Arena globals: the frame pointer is `FM`, the scratch pointer lies in `[FM, SP0]`, the heap pointer is at or
above `P0`. -/
def AW (SP0 P0 FM : BitVec 64) (g : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  g.lookup (ofString "frame_mem_ptr") = some (.val (.word FM)) ∧
  (∃ sp : BitVec 64, g.lookup (ofString "scratch_ptr") = some (.val (.word sp)) ∧ FM.toNat ≤ sp.toNat ∧
    sp.toNat ≤ SP0.toNat) ∧
  (∃ h : BitVec 64, g.lookup (ofString "heap_ptr") = some (.val (.word h)) ∧ P0.toNat ≤ h.toNat)

/-- Arena-safe code keeps the watched word in every outcome and keeps the arena globals on continuing outcomes. -/
def ASafe (SP0 P0 FM w : BitVec 64) (p : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → AW SP0 P0 FM s.globals →
    (evaluateHOLFiniteState s p).2.memory w = s.memory w ∧
    (Continuing (evaluateHOLFiniteState s p).1 → AW SP0 P0 FM (evaluateHOLFiniteState s p).2.globals)

variable {SP0 P0 FM w : BitVec 64}

theorem asafe_mf {p : ProgHOL 64} (h : MemoryFrame p) : ASafe SP0 P0 FM w p := by
  intro F s code aw
  obtain ⟨m,g⟩ := h s code
  exact ⟨by rw [m],fun _ => by rw [g]; exact aw⟩

theorem asafe_seq {p q : ProgHOL 64} (hp : ASafe SP0 P0 FM w p) (hq : ASafe SP0 P0 FM w q) :
    ASafe SP0 P0 FM w (.seq p q) := by
  intro F s code aw
  have h1 := hp s code aw
  have meta' := evaluateHOLFiniteState_metadata s p
  rw [evaluateHOLFiniteState_seq_line780]
  cases r : evaluateHOLFiniteState s p with
  | mk res m =>
    rw [r] at h1 meta'
    cases res with
    | some x => exact h1
    | none =>
      have h2 := hq m (meta'.1.trans code) (h1.2 (Or.inl rfl))
      exact ⟨h2.1.trans h1.1,h2.2⟩

theorem asafe_dec (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64}
    (hb : ASafe SP0 P0 FM w body) : ASafe SP0 P0 FM w (.dec name shape init body) := by
  intro F s code aw
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · exact ⟨rfl,fun _ => aw⟩
  · split
    · exact hb _ (by exact code) (by exact aw)
    · exact ⟨rfl,fun _ => aw⟩

theorem asafe_ite (c : ExpHOL 64) {y n : ProgHOL 64} (hy : ASafe SP0 P0 FM w y) (hn : ASafe SP0 P0 FM w n) :
    ASafe SP0 P0 FM w (.ite c y n) := by
  intro F s code aw
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact hn s code aw
    · exact hy s code aw
  · exact ⟨rfl,fun _ => aw⟩

theorem asafe_while_run (c : ExpHOL 64) (body : ProgHOL 64) (hb : ASafe SP0 P0 FM w body) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (code : s.code = originalRuntimeCode) (aw : AW SP0 P0 FM s.globals) :
    (evaluateHOLFiniteState s (.while c body)).2.memory w = s.memory w ∧
      (Continuing (evaluateHOLFiniteState s (.while c body)).1 →
        AW SP0 P0 FM (evaluateHOLFiniteState s (.while c body)).2.globals) := by
  rw [evaluateHOLFiniteState_while_total]
  split
  · split
    · split
      · exact ⟨rfl,fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h⟩
      · dsimp only
        rw [fixClockHOLFinite_evaluateState]
        have st := hb (decClockHOLFinite s) code aw
        have meta' := evaluateHOLFiniteState_metadata (decClockHOLFinite s) body
        have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
        cases run : evaluateHOLFiniteState (decClockHOLFinite s) body with
        | mk result middle =>
          rw [run] at st meta' remaining
          have smaller : middle.clock < s.clock := by
            change middle.clock ≤ s.clock - 1 at remaining
            omega
          cases result with
          | none =>
            have again := asafe_while_run c body hb middle (meta'.1.trans code) (st.2 (Or.inl rfl))
            exact ⟨again.1.trans st.1,again.2⟩
          | some result =>
            cases result with
            | «continue» =>
              have again := asafe_while_run c body hb middle (meta'.1.trans code) (st.2 (Or.inr (Or.inl rfl)))
              exact ⟨again.1.trans st.1,again.2⟩
            | «break» => exact ⟨st.1,fun _ => st.2 (Or.inr (Or.inr (Or.inl rfl)))⟩
            | returned v => exact st
            | exception _ _ => exact st
            | finalFfi _ => exact st
            | error => exact st
            | timeOut => exact st
    · exact ⟨rfl,fun _ => aw⟩
  · exact ⟨rfl,fun _ => aw⟩
termination_by s.clock

theorem asafe_while (c : ExpHOL 64) {body : ProgHOL 64} (hb : ASafe SP0 P0 FM w body) :
    ASafe SP0 P0 FM w (.while c body) := fun s code aw => asafe_while_run c body hb s code aw

#print axioms asafe_seq
#print axioms asafe_while

theorem asafe_call (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 64)))
    (hinfo : info = some (none,none) ∨ info = none)
    (function : MlS) (arguments : List (ExpHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (hb : ASafe SP0 P0 FM w body) : ASafe SP0 P0 FM w (.call info function arguments) := by
  intro F state code aw
  rw [evaluateHOLFiniteState_call]
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => exact ⟨rfl,fun _ => aw⟩
  | some values =>
    dsimp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => exact ⟨rfl,fun _ => aw⟩
    | some data =>
      obtain ⟨found,callee,foundShape⟩ := data
      dsimp only
      have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body found returnShape
        foundShape values callee (by rw [code]; exact installed) lookup
      subst same
      split
      · exact ⟨rfl,fun _ => aw⟩
      · have frame := hb (callEntryStateHOLFinite state callee) code aw
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at frame
          change bodyPost.memory w = state.memory w ∧ (Continuing rb → AW SP0 P0 FM bodyPost.globals) at frame
          rcases hinfo with rfl | rfl
          · rcases rb with _ | (_ | _ | _ | _ | v | _ | _)
            all_goals (dsimp only)
            all_goals (try split)
            all_goals first
              | exact ⟨frame.1,fun _ => frame.2 (Or.inr (Or.inr (Or.inr ⟨_,rfl⟩)))⟩
              | exact ⟨frame.1,fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h⟩
          · rcases rb with _ | (_ | _ | _ | _ | v | _ | _)
            all_goals (dsimp only)
            all_goals (try split)
            all_goals first
              | exact ⟨frame.1,fun _ => frame.2 (Or.inr (Or.inr (Or.inr ⟨_,rfl⟩)))⟩
              | exact ⟨frame.1,fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h⟩

theorem asafe_decCall (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) {cont : ProgHOL 64}
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (hb : ASafe SP0 P0 FM w body) (hc : ASafe SP0 P0 FM w cont) :
    ASafe SP0 P0 FM w (.decCall name shape function arguments cont) := by
  intro F state code aw
  rw [evaluateHOLFiniteState_decCall_total]
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => exact ⟨rfl,fun _ => aw⟩
  | some values =>
    dsimp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => exact ⟨rfl,fun _ => aw⟩
    | some data =>
      obtain ⟨found,callee,foundShape⟩ := data
      dsimp only
      have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body found returnShape
        foundShape values callee (by rw [code]; exact installed) lookup
      subst same
      split
      · exact ⟨rfl,fun _ => aw⟩
      · have frame := hb (callEntryStateHOLFinite state callee) code aw
        have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) found
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at frame meta'
          change bodyPost.memory w = state.memory w ∧ (Continuing rb → AW SP0 P0 FM bodyPost.globals) at frame
          dsimp only [fixClockHOLFinite]
          rcases rb with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only)
          all_goals (try split)
          all_goals first
            | (refine ⟨(hc _ ?_ ?_).1.trans frame.1,fun hcont => (hc _ ?_ ?_).2 hcont⟩ <;>
                first | exact meta'.1.trans code | exact frame.2 (Or.inr (Or.inr (Or.inr ⟨_,rfl⟩))))
            | exact ⟨frame.1,fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h⟩

#print axioms asafe_call
#print axioms asafe_decCall
end InitECandidate.Runtime
