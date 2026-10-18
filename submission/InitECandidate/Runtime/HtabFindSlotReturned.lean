import InitECandidate.Runtime.PanReturnedPath
import InitECandidate.Runtime.HtabFindSlotBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned declared call: the continuation returned the same value from a
resumed state whose locals are the caller's except the bound name. -/
theorem decCall_returned_locals {F : Type} {s post : PanSemStateFiniteExact 64 F} {name function : MlS}
    {shape : ShapeHOL} {arguments : List (ExpHOL 64)} {continuation : ProgHOL 64} {v : ValueHOL 64}
    (run : evaluateHOLFiniteState s (.decCall name shape function arguments continuation) = (some (.returned v),post)) :
    ∃ resumed inner : PanSemStateFiniteExact 64 F,
      (∀ k, k ≠ name → resumed.locals.lookup k = s.locals.lookup k) ∧
      evaluateHOLFiniteState resumed continuation = (some (.returned v),inner) := by
  rw [evaluateHOLFiniteState_decCall_total] at run
  cases args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments with
  | none => rw [args] at run; simp at run
  | some values =>
    rw [args] at run
    dsimp only at run
    cases lookup : lookupCodeHOLFinite s.code.lookup function values with
    | none => rw [lookup] at run; simp at run
    | some installed =>
      obtain ⟨body,callee,returnShape⟩ := installed
      rw [lookup] at run
      dsimp only at run
      split at run
      · simp at run
      · cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk r bodyPost =>
          rw [bodyRun] at run
          dsimp only [fixClockHOLFinite] at run
          rcases r with _ | (_ | _ | _ | _ | w | _ | _)
          all_goals first
            | (simp at run; done)
            | skip
          simp only [] at run
          split at run
          · obtain ⟨e,p⟩ := Prod.mk.inj run
            refine ⟨_,_,?l,Prod.ext e rfl⟩
            intro k ne
            simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne]
          · simp at run

#print axioms decCall_returned_locals

/-- Partial correctness of returned values through a while loop: an invariant
kept by normal and `continue` iterations (and by the loop tick), and a value
property established by every returning iteration, holds for any value the
whole loop returns. -/
theorem while_returned_invariant (condition : ExpHOL 64) (body : ProgHOL 64)
    (Inv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) (P : ValueHOL 64 → Prop)
    (clockFree : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), Inv s → Inv (decClockHOLFinite s))
    (returns : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v post, Inv s →
      evaluateHOLFiniteState s body = (some (.returned v),post) → P v)
    (keeps : ∀ {F : Type} (s post : PanSemStateFiniteExact 64 F), Inv s →
      (evaluateHOLFiniteState s body = (none,post) ∨ evaluateHOLFiniteState s body = (some .continue,post)) → Inv post) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.clock = n → Inv state →
      ∀ v post, evaluateHOLFiniteState state (.while condition body) = (some (.returned v),post) → P v := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F state clock invariant v post run
    rw [evaluateHOLFiniteState_while_total] at run
    split at run
    · split at run
      · split at run
        · simp at run
        · rename_i nonzero
          dsimp only at run
          rw [fixClockHOLFinite_evaluateState] at run
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk r mid =>
            rw [bodyRun] at run remaining
            have smaller : mid.clock < n := by
              change mid.clock ≤ state.clock - 1 at remaining
              omega
            cases r with
            | none =>
              exact ih mid.clock (by omega) mid rfl (keeps _ mid (clockFree state invariant) (Or.inl bodyRun)) v post run
            | some r =>
              cases r with
              | «continue» =>
                exact ih mid.clock (by omega) mid rfl (keeps _ mid (clockFree state invariant) (Or.inr bodyRun)) v post run
              | returned w =>
                simp at run
                obtain ⟨rfl,_⟩ := run
                exact returns _ w mid (clockFree state invariant) bodyRun
              | _ => simp at run
      · simp at run
    · simp at run

#print axioms while_returned_invariant

/-- A returned declaration: its initializer evaluated and the body returned. -/
theorem dec_returned_eval {F : Type} {s post : PanSemStateFiniteExact 64 F} {name : MlS} {shape : ShapeHOL}
    {initializer : ExpHOL 64} {body : ProgHOL 64} {v : ValueHOL 64}
    (run : evaluateHOLFiniteState s (.dec name shape initializer body) = (some (.returned v),post)) :
    ∃ value inner, @evalHOLExact 64 F _ s.toExact (fun address => Classical.propDecidable (s.memaddrs address))
        initializer = some value ∧
      evaluateHOLFiniteState (setVarHOLFinite name value s) body = (some (.returned v),inner) := by
  rw [evaluateHOLFiniteState_dec_total] at run
  dsimp only at run
  split at run
  · simp at run
  · rename_i value evaluated
    split at run
    · cases inner : evaluateHOLFiniteState (setVarHOLFinite name value s) body with
      | mk r i =>
        rw [inner] at run
        obtain ⟨e,_⟩ := Prod.mk.inj run
        simp only at e
        exact ⟨value,i,evaluated,by rw [inner,e]⟩
    · simp at run

theorem hashProbeStep_not_returned {F : Type} (state : PanSemStateFiniteExact 64 F) (name : MlS) (v : ValueHOL 64) :
    (evaluateHOLFiniteState state (hashProbeStep name)).1 ≠ some (.returned v) := by
  unfold hashProbeStep
  rw [evaluateHOLFiniteState_assign]
  split <;> (try split) <;> simp

theorem hashFindDecision_returned {F : Type} (state inner : PanSemStateFiniteExact 64 F) (index : BitVec 64) (v : ValueHOL 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (run : evaluateHOLFiniteState state hashFindDecision = (some (.returned v),inner)) :
    v = .val (.word index) := by
  cases equalLocal : state.locals.lookup (ofString "eq") with
  | none =>
    unfold hashFindDecision at run
    rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite] at run
    simp [evalHOLExact,equalLocal] at run
  | some value =>
    cases value with
    | val word =>
      cases word with
      | word equal =>
        by_cases zero : equal = 0
        · subst zero
          unfold hashFindDecision at run
          rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite] at run
          have condition : @evalHOLExact 64 F _ state.toExact
              (fun address => Classical.propDecidable (state.memaddrs address))
              (.cmp .notEqual (.var .local (ofString "eq")) (.const 0)) = some (.val (.word (0 : BitVec 64))) := by
            simp [evalHOLExact,equalLocal,Compiler.Encoders.Asm.wordCmpHOL]
          rw [condition] at run
          simp only [if_true,evaluateHOLFiniteState_skip] at run
          exact absurd (congrArg Prod.fst run) (hashProbeStep_not_returned state (ofString "i") v)
        · rw [evaluate_hashFind_match state index equal zero indexLocal equalLocal] at run
          cases run
          rfl
    | _ =>
      unfold hashFindDecision at run
      rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite] at run
      simp [evalHOLExact,equalLocal] at run

theorem return_local_word {F : Type} (s post : PanSemStateFiniteExact 64 F) (x : MlS) (c : BitVec 64) (v : ValueHOL 64)
    (local' : s.locals.lookup x = some (.val (.word c)))
    (run : evaluateHOLFiniteState s (.return (.var .local x)) = (some (.returned v),post)) :
    v = .val (.word c) := by
  rw [evaluateHOLFiniteState_return] at run
  simp only [evalHOLExact,local'] at run
  repeat' (first | (split at run) | skip)
  all_goals simp_all

/-- The masked initial index of a power-of-two table is an in-range word whenever it evaluates. -/
theorem eval_hashFind_index_range {F : Type} (state : PanSemStateFiniteExact 64 F) (capacity : BitVec 64) (bits : Nat)
    (power : capacity.toNat = 2 ^ bits)
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity))) (value : ValueHOL 64)
    (evaluated : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      hashFindIndexExpression = some value) :
    ∃ index : BitVec 64, value = .val (.word index) ∧ index.toNat < capacity.toNat := by
  cases hashLocal : state.locals.lookup (ofString "h") with
  | none => simp [hashFindIndexExpression,evalHOLExact,evalListHOLExact,hashLocal] at evaluated
  | some hv =>
    cases hv with
    | val word =>
      cases word with
      | word hash =>
        rw [eval_hashFind_initial_index state hash capacity hashLocal capLocal] at evaluated
        cases evaluated
        exact ⟨_,rfl,(hashFind_initial_index_bound hash capacity bits power).2⟩
    | _ =>
      simp [hashFindIndexExpression,evalHOLExact,evalListHOLExact,hashLocal,capLocal,valueIsWord,wordOpHOL,wordOp,
        valueWord] at evaluated

/-- Any value returned by the actual lookup body is a word at most the loaded
capacity (a probed in-range index, or the capacity sentinel). -/
theorem htabFindSlot_returned_range {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (table capacity : BitVec 64) (bits : Nat) (power : capacity.toNat = 2 ^ bits)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (domain16 : state.memaddrs (table + 16)) (cell16 : state.memory (table + 16) = .word capacity)
    (v : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_find_slot) = (some (.returned v),post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ capacity.toNat := by
  rw [source_htabFind_header_prefix,evaluate_header_load_scope state _ _ table 16 capacity _ tableLocal domain16 cell16] at run
  generalize hcap : setVarHOLFinite (ofString "cap") (.val (.word capacity)) state = capped at run
  have capped0 : capped.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    rw [← hcap]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  cases inner0 : evaluateHOLFiniteState capped _ with
  | mk r0 p0 =>
    rw [inner0] at run
    obtain ⟨e0,_⟩ := Prod.mk.inj run
    simp only at e0
    subst e0
    obtain ⟨_,_,run1⟩ := dec_returned inner0
    obtain ⟨_,_,run2⟩ := dec_returned run1.1
    obtain ⟨_,_,run3⟩ := dec_returned run2.1
    obtain ⟨_,_,run4⟩ := dec_returned run3.1
    unfold hashFindHashScope at run4
    obtain ⟨resumed,_,agree,run5⟩ := decCall_returned_locals run4.1
    have capR : resumed.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
      rw [agree _ (by decide)]
      simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,capped0,
        show ofString "used" ≠ ofString "cap" by decide,show ofString "keys" ≠ ofString "cap" by decide,
        show ofString "stride" ≠ ofString "cap" by decide,show ofString "klen" ≠ ofString "cap" by decide]
    unfold hashFindIndexScope at run5
    obtain ⟨indexValue,_,evaluated,run6⟩ := dec_returned_eval run5
    obtain ⟨index,rfl,inside⟩ := eval_hashFind_index_range resumed capacity bits power capR indexValue evaluated
    generalize hentry : setVarHOLFinite (ofString "i") (.val (.word index)) resumed = entry at run6
    have capE : entry.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
      rw [← hentry]
      simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,capR,show ofString "i" ≠ ofString "cap" by decide]
    have indexE : entry.locals.lookup (ofString "i") = some (.val (.word index)) := by
      rw [← hentry]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    unfold hashFindTail at run6
    rw [evaluateHOLFiniteState_seq_line780] at run6
    cases loopRun : evaluateHOLFiniteState entry hashFindLoop with
    | mk r m =>
      rw [loopRun] at run6
      cases r with
      | none =>
        have kept := evaluate_avoidsLocal_flowing (ofString "cap") hashFindLoop (by decide) entry
          (by rw [loopRun]; exact Or.inl rfl)
        rw [loopRun] at kept
        simp only at run6
        exact ⟨capacity,return_local_word m _ (ofString "cap") capacity v (by rw [kept]; exact capE) run6,le_refl _⟩
      | some r =>
        simp only at run6
        obtain ⟨e,_⟩ := Prod.mk.inj run6
        simp only [Option.some.injEq] at e
        subst e
        have inv := while_returned_invariant (hashProbeOccupied (ofString "i")) hashFindIteration
          (fun s => ∃ index : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word index)) ∧
            index.toNat < capacity.toNat ∧ s.locals.lookup (ofString "cap") = some (.val (.word capacity)))
          (fun v => ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ capacity.toNat)
          (fun s h => h)
          (by
            intro F s v post ⟨index,iL,inside,capL⟩ run
            unfold hashFindIteration at run
            obtain ⟨resumed,_,agree,contRun⟩ := decCall_returned_locals run
            have := hashFindDecision_returned resumed _ index v (by rw [agree _ (by decide)]; exact iL) contRun
            exact ⟨index,this,Nat.le_of_lt inside⟩)
          (by
            intro F s post ⟨index,iL,inside,capL⟩ flow
            rcases flow with normal | cont
            · have next := hashFindIteration_probe s post index capacity iL capL normal
              have kept := evaluate_avoidsLocal_flowing (ofString "cap") hashFindIteration (by decide) s
                (by rw [normal]; exact Or.inl rfl)
              rw [normal] at kept
              refine ⟨hashProbeNext index capacity,next,?_,by rw [kept]; exact capL⟩
              rw [hashProbeNext_toNat index capacity bits power inside]
              exact Nat.mod_lt _ (by rw [power]; exact Nat.two_pow_pos bits)
            · exact absurd (congrArg Prod.fst cont) (evaluate_noTopContinue hashFindIteration (by decide) s))
        exact inv entry.clock entry rfl ⟨index,indexE,inside,capE⟩ v m (by unfold hashFindLoop at loopRun; exact loopRun)
#print axioms htabFindSlot_returned_range
end InitECandidate.Runtime
