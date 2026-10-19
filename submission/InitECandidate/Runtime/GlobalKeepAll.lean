import InitECandidate.Runtime.NamedGlobalFrame
import InitECandidate.Runtime.GlobalsFrameComposition
import InitECandidate.Runtime.SharedStoreControlFrame
import InitECandidate.Runtime.GlobalKeep
/-!
All globals are unchanged by any program that never assigns a global (nor calls with a global destination) and only
calls functions from a `good` set whose installed bodies pass the same syntactic check (`keepsGA`), at every fuel and
in every outcome (`evaluate_keepsGA`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Syntax that never assigns a global and only calls functions marked `good`, with local or no destinations. -/
def keepsGA (good : MlS → Bool) : ProgHOL 64 → Bool
  | .dec _ _ _ body => keepsGA good body
  | .seq first second => keepsGA good first && keepsGA good second
  | .ite _ yes no => keepsGA good yes && keepsGA good no
  | .while _ body => keepsGA good body
  | .assign .local _ _ => true
  | .store _ _ | .storeByte _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | .extCall _ _ _ _ _ => true
  | .decCall _ _ function _ continuation => good function && keepsGA good continuation
  | .call none function _ => good function
  | .call (some (none,none)) function _ => good function
  | .call (some (some (.local,_),none)) function _ => good function
  | .call (some (none,some (_,_,handler))) function _ => good function && keepsGA good handler
  | .call (some (some (.local,_),some (_,_,handler))) function _ => good function && keepsGA good handler
  | .primitive _ _ _ => true
  | .shMemStore _ _ _ => true
  | _ => false

theorem call_keepsGA {F : Type} (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 64)))
    (function : MlS) (arguments : List (ExpHOL 64)) (state : PanSemStateFiniteExact 64 F)
    (hinfo : info = none ∨ ∃ dest handler, info = some (dest,handler) ∧ (dest = none ∨ ∃ nm, dest = some (.local,nm)))
    (ihBody : ∀ values body callee rs, lookupCodeHOLFinite state.code.lookup function values = some (body,callee,rs) →
      state.clock ≠ 0 →
      (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2.globals = state.globals)
    (ihHandler : ∀ dest hid hv hp, info = some (dest,some (hid,hv,hp)) → ∀ (t : PanSemStateFiniteExact 64 F),
      t.clock < state.clock → t.code = state.code →
      (evaluateHOLFiniteState t hp).2.globals = t.globals) :
    (evaluateHOLFiniteState state (.call info function arguments)).2.globals = state.globals := by
  rw [evaluateHOLFiniteState_call]
  split
  · rfl
  · rename_i values _
    split
    · rfl
    · rename_i body callee rs found
      split
      · rfl
      · rename_i nonzero
        have ih := ihBody values body callee rs found nonzero
        have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) body
        have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
        generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at ih meta' cl
        obtain ⟨r,st⟩ := out
        dsimp only at ih meta' cl ⊢
        change st.clock ≤ state.clock - 1 at cl
        have stc : st.clock < state.clock := by omega
        rcases hinfo with rfl | ⟨dest,handler,rfl,hdest⟩
        · rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
            simp [setKvarHOLFinite,setVarHOLFinite,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
              emptyLocalsHOLFinite,ih] <;> simp_all
        · rcases hdest with rfl | ⟨nm,rfl⟩ <;> rcases handler with _ | ⟨hid,hv,hp⟩ <;>
            rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
            first
              | (refine (ihHandler _ hid hv hp rfl _ (by exact stc) (by exact meta'.1)).trans ih)
              | (simp [setKvarHOLFinite,setVarHOLFinite,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
                  emptyLocalsHOLFinite,ih] <;> simp_all)

theorem shMemStore_globalsA {F : Type} (state : PanSemStateFiniteExact 64 F) (operator : OpSize)
    (address value : ExpHOL 64) :
    (evaluateHOLFiniteState state (.shMemStore operator address value)).2.globals = state.globals := by
  apply HolFiniteMapExact.ext
  funext key
  exact shMemStore_globals state operator address value key

/-- If every installed body of a `good` function passes the checker, then all globals are unchanged by any
program passing the checker, at every fuel and in every outcome. -/
theorem evaluate_keepsGA {F : Type} (good : MlS → Bool)
    (hgood : ∀ function, good function = true → ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
      keepsGA good body = true)
    (program : ProgHOL 64) (supported : keepsGA good program = true) (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state program).2.globals = state.globals := by
  cases shape : program with
  | skip => rw [evaluateHOLFiniteState_skip]
  | dec name kind initializer body =>
    have child : keepsGA good body = true := by simpa only [shape,keepsGA] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · rfl
    · split
      · exact evaluate_keepsGA good hgood body child _ code
      · rfl
  | decCall name kind function arguments continuation =>
    have children : good function = true ∧ keepsGA good continuation = true := by
      simpa only [shape,keepsGA,Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_decCall_total]
    split
    · rfl
    · rename_i values _
      split
      · rfl
      · rename_i body callee rs found
        rw [code] at found
        have bodyOk := hgood function children.1 values body callee rs found
        split
        · rfl
        · rename_i nonzero
          dsimp only
          have ih := evaluate_keepsGA good hgood body bodyOk (callEntryStateHOLFinite state callee) code
          have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) body
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at ih meta' cl
          obtain ⟨r,st⟩ := out
          dsimp only at ih meta' cl ⊢
          change st.clock ≤ state.clock - 1 at cl
          have stCode : st.code = originalRuntimeCode := meta'.1.trans code
          rcases r with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only [fixClockHOLFinite])
          all_goals (try exact ih)
          split
          · have small : (if state.clock - 1 < st.clock then state.clock - 1 else st.clock) < state.clock := by
              split <;> omega
            exact (evaluate_keepsGA good hgood continuation children.2 (setVarHOLFinite name v _) (by exact stCode)).trans ih
          · exact ih
  | assign kind name value =>
    cases kind with
    | global => simp [shape,keepsGA] at supported
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · rfl
      · split <;> rfl
  | seq first second =>
    have children : keepsGA good first = true ∧ keepsGA good second = true := by
      simpa only [shape,keepsGA,Bool.and_eq_true] using supported
    have memory := evaluate_keepsGA good hgood first children.1 state code
    have remaining := evaluateHOLFiniteState_clock_le state first
    have meta' := evaluateHOLFiniteState_metadata state first
    rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at memory remaining meta'
      dsimp only at memory remaining meta'
      cases result with
      | none =>
        have mclock : middle.clock ≤ state.clock := remaining
        exact (evaluate_keepsGA good hgood second children.2 middle (meta'.1.trans code)).trans memory
      | some result => exact memory
  | ite condition yes no =>
    have children : keepsGA good yes = true ∧ keepsGA good no = true := by
      simpa only [shape,keepsGA,Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_keepsGA good hgood no children.2 state code
      · exact evaluate_keepsGA good hgood yes children.1 state code
    · rfl
  | «while» condition body =>
    have child : keepsGA good body = true := by simpa only [shape,keepsGA] using supported
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rfl
        · rename_i nonzero
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have memory := evaluate_keepsGA good hgood body child (decClockHOLFinite state) code
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          have meta' := evaluateHOLFiniteState_metadata (decClockHOLFinite state) body
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk result middle =>
            rw [bodyRun] at memory remaining meta'
            dsimp only at memory remaining meta'
            have smaller : middle.clock < state.clock := by
              change middle.clock ≤ state.clock - 1 at remaining
              omega
            have mc : middle.code = originalRuntimeCode := meta'.1.trans code
            cases result with
            | none => exact (evaluate_keepsGA good hgood (.while condition body)
                (by simpa [keepsGA] using child) middle mc).trans memory
            | some result =>
              cases result with
              | «continue» => exact (evaluate_keepsGA good hgood (.while condition body)
                  (by simpa [keepsGA] using child) middle mc).trans memory
              | «break» => exact memory
              | returned value => exact memory
              | exception exception value => exact memory
              | finalFfi ffi => exact memory
              | error => exact memory
              | timeOut => exact memory
      · rfl
    · rfl
  | «break» => rw [evaluateHOLFiniteState_break]
  | «continue» => rw [evaluateHOLFiniteState_continue]
  | annot tag text => rw [evaluateHOLFiniteState_annot]
  | raise name value =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> rfl
    · rfl
  | «return» value =>
    rw [evaluateHOLFiniteState_return]
    split
    · rfl
    · split <;> rfl
  | store destination value =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | storeByte destination value =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | extCall name a b c d => exact originalGlobalsFrame_external name a b c d state code
  | call info function arguments =>
    have hk : good function = true ∧ (info = none ∨ ∃ dest handler, info = some (dest,handler) ∧
        (dest = none ∨ ∃ nm, dest = some (.local,nm))) ∧
        ∀ dest hid hv hp, info = some (dest,some (hid,hv,hp)) → keepsGA good hp = true := by
      rcases info with _ | ⟨_ | ⟨kind,nm⟩,_ | ⟨hid,hv,hp⟩⟩
      · exact ⟨by simpa [shape,keepsGA] using supported,Or.inl rfl,fun _ _ _ _ h => by cases h⟩
      · exact ⟨by simpa [shape,keepsGA] using supported,Or.inr ⟨none,none,rfl,Or.inl rfl⟩,fun _ _ _ _ h => by cases h⟩
      · simp [shape,keepsGA] at supported
        exact ⟨supported.1,Or.inr ⟨none,_,rfl,Or.inl rfl⟩,fun _ _ _ _ h => by cases h; exact supported.2⟩
      · cases kind
        · exact ⟨by simpa [shape,keepsGA] using supported,Or.inr ⟨_,none,rfl,Or.inr ⟨nm,rfl⟩⟩,fun _ _ _ _ h => by cases h⟩
        · simp [shape,keepsGA] at supported
      · cases kind
        · simp [shape,keepsGA] at supported
          exact ⟨supported.1,Or.inr ⟨_,_,rfl,Or.inr ⟨nm,rfl⟩⟩,fun _ _ _ _ h => by cases h; exact supported.2⟩
        · simp [shape,keepsGA] at supported
    refine call_keepsGA info function arguments state hk.2.1 (fun values body callee rs found nonzero => ?_)
      (fun dest hid hv hp hi t tlt tcode => ?_)
    · rw [code] at found
      exact evaluate_keepsGA good hgood body (hgood function hk.1 values body callee rs found)
        (callEntryStateHOLFinite state callee) code
    · exact evaluate_keepsGA good hgood hp (hk.2.2 dest hid hv hp hi) t (tcode.trans code)
  | primitive name operator arguments =>
    rw [evaluateHOLFiniteState_primitive]
    split
    · rfl
    · split
      · rfl
      · split <;> rfl
  | shMemStore operator address value =>
    exact shMemStore_globalsA state operator address value
  | _ => simp [shape,keepsGA] at supported
termination_by (state.clock,sizeOf program)
decreasing_by
  all_goals
    simp_wf
    apply lex_of
    try subst shape
    try simp only [setVarHOLFinite,decClockHOLFinite,callEntryStateHOLFinite,ProgHOL.seq.sizeOf_spec,
      ProgHOL.ite.sizeOf_spec,ProgHOL.dec.sizeOf_spec,ProgHOL.while.sizeOf_spec,ProgHOL.decCall.sizeOf_spec,true_and]
    first
      | exact Or.inl small
      | (simp only [callEntryStateHOLFinite] at small; exact Or.inl small)
      | omega
      | (by_cases hc : state.clock = 0
         · right; refine ⟨by omega,?_⟩; simp +arith
         · left; omega)
      | (rcases Nat.lt_or_eq_of_le mclock with h | h
         · exact Or.inl h
         · right; refine ⟨h,?_⟩; simp +arith)
      | (right; refine ⟨rfl,?_⟩; simp +arith)

#print axioms call_keepsGA
#print axioms evaluate_keepsGA
end InitECandidate.Runtime
