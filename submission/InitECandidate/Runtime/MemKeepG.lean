import InitECandidate.Runtime.NamedGlobalFrame
import InitECandidate.Runtime.GlobalsFrameComposition
import InitECandidate.Runtime.SharedStoreControlFrame
import InitECandidate.Runtime.AccountLeafAnyAlloc
import InitECandidate.Runtime.GlobalKeep
/-!
Memory is unchanged by any program that never stores to memory (shared-memory stores and zero-length external calls
are allowed; primitive operations only assign locals) and only calls functions from a `good` set whose installed bodies pass the same syntactic check
(`keepsM`), at every fuel and in every outcome (`evaluate_keepsM`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Memory checker: no memory stores (shared-memory stores and zero-length external calls are allowed), and every
called function is `good`. -/
def keepsM (good : MlS → Bool) : ProgHOL 64 → Bool
  | .dec _ _ _ body => keepsM good body
  | .seq first second => keepsM good first && keepsM good second
  | .ite _ yes no => keepsM good yes && keepsM good no
  | .while _ body => keepsM good body
  | .assign _ _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | .extCall _ _ _ _ (.const c) => c == 0
  | .decCall _ _ function _ continuation => good function && keepsM good continuation
  | .call none function _ => good function
  | .call (some (_,none)) function _ => good function
  | .call (some (_,some (_,_,handler))) function _ => good function && keepsM good handler
  | .shMemStore _ _ _ => true
  | .primitive _ _ _ => true
  | _ => false

theorem call_keepsM {F : Type} (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 64)))
    (function : MlS) (arguments : List (ExpHOL 64)) (state : PanSemStateFiniteExact 64 F)
    (ihBody : ∀ values body callee rs, lookupCodeHOLFinite state.code.lookup function values = some (body,callee,rs) →
      state.clock ≠ 0 →
      (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2.memory = state.memory)
    (ihHandler : ∀ dest hid hv hp, info = some (dest,some (hid,hv,hp)) → ∀ (t : PanSemStateFiniteExact 64 F),
      t.clock < state.clock → t.code = state.code →
      (evaluateHOLFiniteState t hp).2.memory = t.memory) :
    (evaluateHOLFiniteState state (.call info function arguments)).2.memory = state.memory := by
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
        rcases info with _ | ⟨dest,_ | ⟨hid,hv,hp⟩⟩
        · rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
            simp [setKvarHOLFinite,setVarHOLFinite,setGlobalHOLFinite,emptyLocalsHOLFinite,ih] <;> simp_all <;>
            (split <;> rfl)
        · rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
            simp [setKvarHOLFinite,setVarHOLFinite,setGlobalHOLFinite,emptyLocalsHOLFinite,ih] <;> simp_all <;>
            (split <;> rfl)
        · rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
            first
              | (refine (ihHandler _ hid hv hp rfl _ (by exact stc) (by exact meta'.1)).trans ih)
              | (simp [setKvarHOLFinite,setVarHOLFinite,setGlobalHOLFinite,emptyLocalsHOLFinite,ih] <;> simp_all <;>
                  (split <;> rfl))


#print axioms call_keepsM

/-- If every installed body of a `good` function passes the checker, then memory is unchanged by any
program passing the checker, at every fuel and in every outcome. -/
theorem evaluate_keepsM {F : Type} (good : MlS → Bool)
    (hgood : ∀ function, good function = true → ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
      keepsM good body = true)
    (program : ProgHOL 64) (supported : keepsM good program = true) (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state program).2.memory = state.memory := by
  cases shape : program with
  | skip => rw [evaluateHOLFiniteState_skip]
  | dec name kind initializer body =>
    have child : keepsM good body = true := by simpa only [shape,keepsM] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · rfl
    · split
      · exact evaluate_keepsM good hgood body child _ code
      · rfl
  | decCall name kind function arguments continuation =>
    have children : good function = true ∧ keepsM good continuation = true := by
      simpa only [shape,keepsM,Bool.and_eq_true] using supported
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
          have ih := evaluate_keepsM good hgood body bodyOk (callEntryStateHOLFinite state callee) code
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
            exact (evaluate_keepsM good hgood continuation children.2 (setVarHOLFinite name v _) (by exact stCode)).trans ih
          · exact ih
  | assign kind name value => exact evaluate_assign_memory state kind name value
  | seq first second =>
    have children : keepsM good first = true ∧ keepsM good second = true := by
      simpa only [shape,keepsM,Bool.and_eq_true] using supported
    have memory := evaluate_keepsM good hgood first children.1 state code
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
        exact (evaluate_keepsM good hgood second children.2 middle (meta'.1.trans code)).trans memory
      | some result => exact memory
  | ite condition yes no =>
    have children : keepsM good yes = true ∧ keepsM good no = true := by
      simpa only [shape,keepsM,Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_keepsM good hgood no children.2 state code
      · exact evaluate_keepsM good hgood yes children.1 state code
    · rfl
  | «while» condition body =>
    have child : keepsM good body = true := by simpa only [shape,keepsM] using supported
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rfl
        · rename_i nonzero
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have memory := evaluate_keepsM good hgood body child (decClockHOLFinite state) code
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
            | none => exact (evaluate_keepsM good hgood (.while condition body)
                (by simpa [keepsM] using child) middle mc).trans memory
            | some result =>
              cases result with
              | «continue» => exact (evaluate_keepsM good hgood (.while condition body)
                  (by simpa [keepsM] using child) middle mc).trans memory
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
  | extCall name a b c d =>
    cases d with
    | const k =>
      have k0 : k = 0 := by simpa [shape,keepsM] using supported
      subst k0
      exact memKeep_extCall_zero name a b c state code
    | _ => simp [shape,keepsM] at supported
  | call info function arguments =>
    have hk : good function = true ∧
        ∀ dest hid hv hp, info = some (dest,some (hid,hv,hp)) → keepsM good hp = true := by
      rcases info with _ | ⟨dest,_ | ⟨hid,hv,hp⟩⟩
      · exact ⟨by simpa [shape,keepsM] using supported,fun _ _ _ _ h => by cases h⟩
      · exact ⟨by simpa [shape,keepsM] using supported,fun _ _ _ _ h => by cases h⟩
      · simp [shape,keepsM] at supported
        exact ⟨supported.1,fun _ _ _ _ h => by cases h; exact supported.2⟩
    refine call_keepsM info function arguments state (fun values body callee rs found nonzero => ?_)
      (fun dest hid hv hp hi t tlt tcode => ?_)
    · rw [code] at found
      exact evaluate_keepsM good hgood body (hgood function hk.1 values body callee rs found)
        (callEntryStateHOLFinite state callee) code
    · exact evaluate_keepsM good hgood hp (hk.2 dest hid hv hp hi) t (tcode.trans code)
  | shMemStore operator address value => exact memKeep_shMemStore operator address value state code
  | primitive name operator arguments =>
    rw [evaluateHOLFiniteState_primitive]
    split
    · rfl
    · split
      · rfl
      · split <;> rfl
  | _ => simp [shape,keepsM] at supported
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


#print axioms evaluate_keepsM
end InitECandidate.Runtime
