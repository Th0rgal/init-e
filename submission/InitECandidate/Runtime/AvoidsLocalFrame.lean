import InitECandidate.Runtime.NamedGlobalFrame
import InitECandidate.Runtime.ByteStoresControlFrame
import InitECandidate.Runtime.StoreControlFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Programs whose normal completion cannot rebind the local `key`. -/
def avoidsLocal (key : MlS) : ProgHOL 64 → Bool
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | .store _ _ | .storeByte _ _ | .extCall _ _ _ _ _ => true
  | .assign .global _ _ => true
  | .assign .local name _ => !(name == key)
  | .primitive name _ _ => !(name == key)
  | .seq first second => avoidsLocal key first && avoidsLocal key second
  | .ite _ yes no => avoidsLocal key yes && avoidsLocal key no
  | .dec name _ _ body => (name == key) || avoidsLocal key body
  | .while _ body => avoidsLocal key body
  | .call none _ _ => true
  | .call (some (none,none)) _ _ => true
  | .call (some (some (.global,_),none)) _ _ => true
  | .call (some (some (.local,name),none)) _ _ => !(name == key)
  | .decCall name _ _ _ continuation => (name == key) || avoidsLocal key continuation
  | _ => false

theorem resVarEq_lookup {width : Nat} [NeZero width] (map : HolFiniteMapExact MlS (ValueHOL width))
    (name key : MlS) (saved : Option (ValueHOL width)) :
    (HolFiniteMapExact.resVarEq map (name,saved)).lookup key = if key = name then saved else map.lookup key := by
  cases saved <;> by_cases h : key = name <;>
    simp [lookup_resVarEq_toExact,resVarHOLExact,FDOMSUB_HOL,FUPDATE_HOL,h]

def Flowing (result : Option (PanSemResultExact 64)) : Prop :=
  result = none ∨ result = some .break ∨ result = some .continue

theorem dec_flowing {F : Type} {s post : PanSemStateFiniteExact 64 F} {name : MlS} {shape : ShapeHOL}
    {initializer : ExpHOL 64} {body : ProgHOL 64} {r : Option (PanSemResultExact 64)} (flow : Flowing r)
    (run : evaluateHOLFiniteState s (.dec name shape initializer body) = (r,post)) :
    ∃ value inner, evaluateHOLFiniteState (setVarHOLFinite name value s) body = (r,inner) ∧
      post.locals = HolFiniteMapExact.resVarEq inner.locals (name,s.locals.lookup name) := by
  rw [evaluateHOLFiniteState_dec_total] at run
  dsimp only at run
  split at run
  · simp at run; obtain ⟨rfl,_⟩ := run; rcases flow with h|h|h <;> simp at h
  · rename_i value _
    split at run
    · cases h : evaluateHOLFiniteState (setVarHOLFinite name value s) body with
      | mk r' inner =>
        rw [h] at run
        simp only [Prod.mk.injEq] at run
        obtain ⟨e,p⟩ := run
        subst e
        exact ⟨value,inner,h,by rw [← p]⟩
    · simp at run; obtain ⟨rfl,_⟩ := run; rcases flow with h|h|h <;> simp at h

theorem while_flowing {F : Type} {s post : PanSemStateFiniteExact 64 F} {condition : ExpHOL 64} {body : ProgHOL 64}
    {r : Option (PanSemResultExact 64)} (flow : Flowing r)
    (run : evaluateHOLFiniteState s (.while condition body) = (r,post)) :
    post = s ∨ ∃ mid r1, evaluateHOLFiniteState (decClockHOLFinite s) body = (r1,mid) ∧ Flowing r1 ∧
      mid.clock < s.clock ∧ ((r1 = some .break ∧ post = mid) ∨
        ((r1 = none ∨ r1 = some .continue) ∧ evaluateHOLFiniteState mid (.while condition body) = (r,post))) := by
  rw [evaluateHOLFiniteState_while_total] at run
  split at run
  · split at run
    · split at run
      · simp at run; obtain ⟨rfl,_⟩ := run; rcases flow with h|h|h <;> simp at h
      · rename_i nonzero
        dsimp only at run
        rw [fixClockHOLFinite_evaluateState] at run
        have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
        cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite s) body with
        | mk r1 mid =>
          rw [bodyRun] at run remaining
          have smaller : mid.clock < s.clock := by
            change mid.clock ≤ s.clock - 1 at remaining
            omega
          right
          cases r1 with
          | none => exact ⟨mid,none,rfl,Or.inl rfl,smaller,Or.inr ⟨Or.inl rfl,run⟩⟩
          | some r1 =>
            cases r1 with
            | «continue» => exact ⟨mid,some .continue,rfl,Or.inr (Or.inr rfl),smaller,Or.inr ⟨Or.inr rfl,run⟩⟩
            | «break» =>
              simp at run; obtain ⟨rfl,rfl⟩ := run
              exact ⟨mid,some .break,rfl,Or.inr (Or.inl rfl),smaller,Or.inl ⟨rfl,rfl⟩⟩
            | _ => simp at run; obtain ⟨rfl,_⟩ := run; rcases flow with h|h|h <;> simp at h
    · simp at run; exact Or.inl run.2.symm
  · simp at run; obtain ⟨rfl,_⟩ := run; rcases flow with h|h|h <;> simp at h

theorem decCall_flowing {F : Type} {s post : PanSemStateFiniteExact 64 F} {name function : MlS}
    {shape : ShapeHOL} {arguments : List (ExpHOL 64)} {continuation : ProgHOL 64}
    {r : Option (PanSemResultExact 64)} (flow : Flowing r)
    (run : evaluateHOLFiniteState s (.decCall name shape function arguments continuation) = (r,post)) :
    ∃ (w : ValueHOL 64) (resumed inner : PanSemStateFiniteExact 64 F),
      (∀ k, k ≠ name → resumed.locals.lookup k = s.locals.lookup k) ∧ resumed.clock < s.clock ∧
      evaluateHOLFiniteState resumed continuation = (r,inner) ∧
      post.locals = HolFiniteMapExact.resVarEq inner.locals (name,s.locals.lookup name) := by
  rw [evaluateHOLFiniteState_decCall_total] at run
  unfold Flowing at flow
  cases args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments with
  | none => rw [args] at run; simp at run; obtain ⟨rfl,_⟩ := run; simp at flow
  | some values =>
    rw [args] at run
    dsimp only at run
    cases lookup : lookupCodeHOLFinite s.code.lookup function values with
    | none => rw [lookup] at run; simp at run; obtain ⟨rfl,_⟩ := run; simp at flow
    | some installed =>
      obtain ⟨body,callee,returnShape⟩ := installed
      rw [lookup] at run
      dsimp only at run
      split at run
      · simp at run; obtain ⟨rfl,_⟩ := run; simp at flow
      · rename_i nonzero
        have remaining := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk r1 bodyPost =>
          rw [bodyRun] at run remaining
          dsimp only [fixClockHOLFinite] at run
          rcases r1 with _ | (_ | _ | _ | _ | w | _ | _)
          all_goals first
            | (simp at run; obtain ⟨rfl,_⟩ := run; simp at flow; done)
            | skip
          simp only [] at run
          split at run
          · obtain ⟨e,p⟩ := Prod.mk.inj run
            refine ⟨w,_,_,?rl,?ck,Prod.ext e rfl,by rw [← p]⟩
            case rl =>
              intro k different
              simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different]
            case ck =>
              change (if _ then _ else _) < s.clock
              change bodyPost.clock ≤ s.clock - 1 at remaining
              split <;> omega
          · simp at run; obtain ⟨rfl,_⟩ := run; simp at flow

/-- A program that avoids `key` leaves the local `key` bound exactly as before
whenever it completes normally or with break/continue, including through
calls, scoped declarations and loops. -/
theorem evaluate_avoidsLocal_flowing {F : Type} (key : MlS) (program : ProgHOL 64)
    (supported : avoidsLocal key program = true) (state : PanSemStateFiniteExact 64 F)
    (flow : Flowing (evaluateHOLFiniteState state program).1) :
    (evaluateHOLFiniteState state program).2.locals.lookup key = state.locals.lookup key := by
  cases shape : program with
  | skip => rw [evaluateHOLFiniteState_skip]
  | «break» => rw [evaluateHOLFiniteState_break]
  | «continue» => rw [evaluateHOLFiniteState_continue]
  | annot tag text => rw [evaluateHOLFiniteState_annot]
  | raise name value =>
    rw [shape,evaluateHOLFiniteState_raise] at flow
    unfold Flowing at flow
    split at flow
    · dsimp only at flow; split at flow <;> simp at flow
    · simp at flow
  | «return» value =>
    rw [shape,evaluateHOLFiniteState_return] at flow
    unfold Flowing at flow
    split at flow
    · simp at flow
    · split at flow <;> simp at flow
  | store destination value => rw [(evaluate_store_control_frame state destination value).2.1]
  | storeByte destination value => rw [(evaluate_storeByte_control_frame state destination value).2.2.1]
  | extCall function a b c d =>
    rw [shape,evaluateHOLFiniteState_extCall_source] at flow
    rw [evaluateHOLFiniteState_extCall_source]
    unfold Flowing at flow
    repeat' first | split | rfl
    all_goals simp_all [emptyLocalsHOLFinite]
  | assign kind name value =>
    rw [evaluateHOLFiniteState_assign]
    cases kind with
    | global =>
      split
      · rfl
      · split
        · simp [setKvarHOLFinite,setGlobalHOLFinite]
        · rfl
    | «local» =>
      have different : name ≠ key := by simpa [shape,avoidsLocal] using supported
      split
      · rfl
      · split
        · simp [setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different]
        · rfl
  | primitive name operator arguments =>
    have different : name ≠ key := by simpa [shape,avoidsLocal] using supported
    rw [evaluateHOLFiniteState_primitive]
    repeat' first | split | rfl
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different]
  | seq first second =>
    have children : avoidsLocal key first = true ∧ avoidsLocal key second = true := by
      simpa only [shape,avoidsLocal,Bool.and_eq_true] using supported
    rw [shape,evaluateHOLFiniteState_seq_line780] at flow
    rw [evaluateHOLFiniteState_seq_line780]
    have remaining := evaluateHOLFiniteState_clock_le state first
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at flow remaining
      have one := evaluate_avoidsLocal_flowing key first children.1 state
      rw [firstRun] at one
      cases result with
      | none => exact (evaluate_avoidsLocal_flowing key second children.2 middle flow).trans (one (Or.inl rfl))
      | some r => exact one flow
  | ite condition yes no =>
    have children : avoidsLocal key yes = true ∧ avoidsLocal key no = true := by
      simpa only [shape,avoidsLocal,Bool.and_eq_true] using supported
    rw [shape,evaluateHOLFiniteState_ite] at flow
    rw [evaluateHOLFiniteState_ite]
    split
    · rename_i flag hflag
      rw [hflag] at flow
      dsimp only at flow ⊢
      split
      · rw [if_pos (by assumption)] at flow
        exact evaluate_avoidsLocal_flowing key no children.2 state flow
      · rw [if_neg (by assumption)] at flow
        exact evaluate_avoidsLocal_flowing key yes children.1 state flow
    · rfl
  | dec name kind initializer body =>
    cases run : evaluateHOLFiniteState state (.dec name kind initializer body) with
    | mk result post =>
      rw [shape,run] at flow
      dsimp only at flow
      obtain ⟨value,inner,bodyRun,locals⟩ := dec_flowing flow run
      change post.locals.lookup key = _
      rw [locals,resVarEq_lookup]
      by_cases same : key = name
      · rw [if_pos same,same]
      · rw [if_neg same]
        have child : avoidsLocal key body = true := by
          have := supported; simp [shape,avoidsLocal] at this
          rcases this with h | h
          · exact absurd h.symm same
          · exact h
        have inner' := evaluate_avoidsLocal_flowing key body child (setVarHOLFinite name value state) (by rw [bodyRun]; exact flow)
        rw [bodyRun] at inner'
        rw [inner']
        simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,same,Ne.symm same]
  | «while» condition body =>
    have child : avoidsLocal key body = true := by simpa only [shape,avoidsLocal] using supported
    cases run : evaluateHOLFiniteState state (.while condition body) with
    | mk result post =>
      rw [shape,run] at flow
      dsimp only at flow
      change post.locals.lookup key = _
      rcases while_flowing flow run with rfl | ⟨mid,r1,bodyRun,bodyFlow,smaller,exit⟩
      · rfl
      · have one := evaluate_avoidsLocal_flowing key body child (decClockHOLFinite state) (by rw [bodyRun]; exact bodyFlow)
        rw [bodyRun] at one
        change mid.locals.lookup key = state.locals.lookup key at one
        rcases exit with ⟨_,rfl⟩ | ⟨_,loop⟩
        · exact one
        · have two := evaluate_avoidsLocal_flowing key (.while condition body) (by simpa [avoidsLocal] using child) mid
            (by rw [loop]; exact flow)
          rw [loop] at two
          exact two.trans one
  | call info function arguments =>
    have dest : info = none ∨ info = some (none,none) ∨ (∃ g, info = some (some (.global,g),none)) ∨
        (∃ n, n ≠ key ∧ info = some (some (.local,n),none)) := by
      rcases info with _ | ⟨_ | ⟨kind,n⟩,_ | h⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · simp [shape,avoidsLocal] at supported
      · cases kind
        · simp [shape,avoidsLocal] at supported
          exact Or.inr (Or.inr (Or.inr ⟨n,supported,rfl⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨n,rfl⟩))
      · cases kind <;> simp [shape,avoidsLocal] at supported
    rw [shape,evaluateHOLFiniteState_call] at flow
    rw [evaluateHOLFiniteState_call]
    unfold Flowing at flow
    rcases dest with rfl | rfl | ⟨g,rfl⟩ | ⟨n,different,rfl⟩
    all_goals dsimp only at flow ⊢
    all_goals
      repeat' first | split | rfl
    all_goals simp_all [setKvarHOLFinite,setVarHOLFinite,setGlobalHOLFinite,emptyLocalsHOLFinite,
      HolFiniteMapExact.lookup_update,FUPDATE]
  | decCall name shape' function arguments continuation =>
    cases run : evaluateHOLFiniteState state (.decCall name shape' function arguments continuation) with
    | mk result post =>
      rw [shape,run] at flow
      dsimp only at flow
      change post.locals.lookup key = _
      obtain ⟨w,resumed,inner,rl,smaller,contRun,locals⟩ := decCall_flowing flow run
      rw [locals,resVarEq_lookup]
      by_cases same : key = name
      · rw [if_pos same,same]
      · rw [if_neg same]
        have child : avoidsLocal key continuation = true := by
          have := supported; simp [shape,avoidsLocal] at this
          rcases this with h | h
          · exact absurd h.symm same
          · exact h
        have inner' := evaluate_avoidsLocal_flowing key continuation child resumed (by rw [contRun]; exact flow)
        rw [contRun] at inner'
        rw [inner',rl key same]
  | _ => simp [shape,avoidsLocal] at supported
termination_by (state.clock,sizeOf program)
decreasing_by all_goals simp_all [decClockHOLFinite,setVarHOLFinite] <;> omega

#print axioms evaluate_avoidsLocal_flowing
end InitECandidate.Runtime
