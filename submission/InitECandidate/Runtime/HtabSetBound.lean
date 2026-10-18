import InitECandidate.Runtime.HtabGrowFrame
import InitECandidate.Runtime.OriginalHashSetCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Under the original code, every evaluation of the program leaves memory and globals unchanged. -/
def MemoryFrame (program : ProgHOL 64) : Prop :=
  ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
    (evaluateHOLFiniteState state program).2.memory = state.memory ∧
      (evaluateHOLFiniteState state program).2.globals = state.globals

theorem memoryFrame_leaf (program : ProgHOL 64) (supported : readOnlyMemory program = true) : MemoryFrame program :=
  fun state _ => ⟨evaluate_readOnly_memory program supported state,evaluate_readOnly_globals program supported state⟩

theorem memoryFrame_seq {first second : ProgHOL 64} (a : MemoryFrame first) (b : MemoryFrame second) :
    MemoryFrame (.seq first second) := by
  intro F state code
  have frame := a state code
  have metadata := evaluateHOLFiniteState_metadata state first
  rw [evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState state first with
  | mk result middle =>
    rw [run] at frame metadata
    cases result with
    | none =>
      obtain ⟨m2,g2⟩ := b middle (metadata.1.trans code)
      exact ⟨m2.trans frame.1,g2.trans frame.2⟩
    | some _ => exact frame

theorem memoryFrame_dec (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64) {body : ProgHOL 64}
    (frame : MemoryFrame body) : MemoryFrame (.dec name shape initializer body) := by
  intro F state code
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · exact ⟨rfl,rfl⟩
  · split
    · exact frame _ code
    · exact ⟨rfl,rfl⟩

theorem memoryFrame_ite (condition : ExpHOL 64) {yes no : ProgHOL 64} (a : MemoryFrame yes) (b : MemoryFrame no) :
    MemoryFrame (.ite condition yes no) := by
  intro F state code
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact b state code
    · exact a state code
  · exact ⟨rfl,rfl⟩

theorem evaluate_while_memory_frame (condition : ExpHOL 64) (body : ProgHOL 64)
    (frame : MemoryFrame body) {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state (.while condition body)).2.memory = state.memory ∧
      (evaluateHOLFiniteState state (.while condition body)).2.globals = state.globals := by
  rw [evaluateHOLFiniteState_while_total]
  split
  · split
    · split
      · exact ⟨rfl,rfl⟩
      · dsimp only
        rw [fixClockHOLFinite_evaluateState]
        have step := frame (decClockHOLFinite state) code
        have metadata := evaluateHOLFiniteState_metadata (decClockHOLFinite state) body
        have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
        cases run : evaluateHOLFiniteState (decClockHOLFinite state) body with
        | mk result middle =>
          rw [run] at step metadata remaining
          have smaller : middle.clock < state.clock := by
            change middle.clock ≤ state.clock - 1 at remaining
            omega
          have again := fun (_ : True) => evaluate_while_memory_frame condition body frame middle (metadata.1.trans code)
          cases result with
          | none => exact ⟨(again trivial).1.trans step.1,(again trivial).2.trans step.2⟩
          | some result =>
            cases result with
            | «continue» => exact ⟨(again trivial).1.trans step.1,(again trivial).2.trans step.2⟩
            | «break» => exact step
            | returned _ => exact step
            | exception _ _ => exact step
            | finalFfi _ => exact step
            | error => exact step
            | timeOut => exact step
    · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
termination_by state.clock

theorem memoryFrame_while (condition : ExpHOL 64) {body : ProgHOL 64} (frame : MemoryFrame body) :
    MemoryFrame (.while condition body) :=
  fun state code => evaluate_while_memory_frame condition body frame state code

theorem memoryFrame_decCall (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64))
    {continuation : ProgHOL 64} (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (bodyFrame : MemoryFrame body) (tailFrame : MemoryFrame continuation) :
    MemoryFrame (.decCall name shape function arguments continuation) := by
  intro F state code
  rw [evaluateHOLFiniteState_decCall_total]
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
      · have frame := bodyFrame (callEntryStateHOLFinite state callee) code
        have metadata := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) found
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk r bodyPost =>
          rw [bodyRun] at frame metadata
          change bodyPost.memory = state.memory ∧ bodyPost.globals = state.globals at frame
          dsimp only [fixClockHOLFinite]
          cases r with
          | none => exact frame
          | some r =>
            cases r with
            | returned w =>
              dsimp only
              split
              · exact ⟨Eq.trans (tailFrame _ (by exact metadata.1.trans code)).1 frame.1,
                  Eq.trans (tailFrame _ (by exact metadata.1.trans code)).2 frame.2⟩
              · exact frame
            | _ => exact frame

/-- The original lookup never changes memory or globals, in any outcome. -/
theorem htabFindSlot_memoryFrame : MemoryFrame (sourceFunctionBody Guest.guestFn_htab_find_slot) := by
  rw [source_htabFind_header_prefix]
  refine memoryFrame_dec _ _ _ (memoryFrame_dec _ _ _ (memoryFrame_dec _ _ _ (memoryFrame_dec _ _ _
    (memoryFrame_dec _ _ _ ?_))))
  unfold hashFindHashScope
  refine memoryFrame_decCall _ _ _ _ _ _ _ originalRuntimeCode_hash_lookup (memoryFrame_leaf _ htabHash_readOnly) ?_
  unfold hashFindIndexScope hashFindTail hashFindLoop
  refine memoryFrame_dec _ _ _ (memoryFrame_seq (memoryFrame_while _ ?_) (memoryFrame_leaf _ (by decide)))
  unfold hashFindIteration
  exact memoryFrame_decCall _ _ _ _ _ _ _ originalRuntimeCode_memeq_lookup (memoryFrame_leaf _ memeq_readOnlyMemory)
    (memoryFrame_leaf _ hashFindDecision_readOnly)

#print axioms htabFindSlot_memoryFrame

open InitECandidate.Proofs.FrontendCodecComputation in
def htabSetDecoded : ProgHOL 64 :=
  match declToHOLStructural Guest.guestFn_htab_set with | .function fn => fn.body | _ => .skip

def htabSetUpdate : ProgHOL 64 :=
  match htabSetDecoded with | .decCall _ _ _ _ (.seq update _) => update | _ => .skip

def htabSetGuard : ExpHOL 64 :=
  match htabSetDecoded with | .decCall _ _ _ _ (.seq _ (.seq (.ite guard _ _) _)) => guard | _ => .const 0

theorem source_htabSet_body : sourceFunctionBody Guest.guestFn_htab_set =
    .decCall (ofString "i") .one (ofString "htab_find_slot") [.var .local (ofString "t"),.var .local (ofString "key")]
      (.seq htabSetUpdate
        (.seq (.ite htabSetGuard (.call (some (none,none)) (ofString "htab_grow") [.var .local (ofString "t")]) .skip)
          (.seq (.call (some (none,none)) (ofString "htab_insert_raw")
              [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")])
            (.return (.const 0))))) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem htabSetUpdate_straight : extStraightLine htabSetUpdate = true := by decide

theorem return_not_none {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.return e)).1 ≠ none := by
  rw [evaluateHOLFiniteState_return]
  split <;> (try split) <;> simp

/-- The existing-key update branch finishes normally only by skipping. -/
theorem htabSetUpdate_normal {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState s htabSetUpdate = (none,next)) : next = s := by
  have shape : htabSetUpdate = .ite (.cmp .notEqual (.var .local (ofString "i"))
      (.load .one (.op .add [.var .local (ofString "t"),.const 16])))
      (.seq (.store (.op .add [.load .one (.op .add [.var .local (ofString "t"),.const 40]),
          .panop .mul [.var .local (ofString "i"),.const 8]]) (.var .local (ofString "value"))) (.return (.const 0))) .skip := rfl
  rw [shape,evaluateHOLFiniteState_ite] at run
  split at run
  · split at run
    · rw [evaluateHOLFiniteState_skip] at run
      exact (Prod.mk.inj run).2.symm
    · rw [evaluateHOLFiniteState_seq_line780] at run
      cases st : evaluateHOLFiniteState s (.store (.op .add [.load .one (.op .add [.var .local (ofString "t"),.const 40]),
          .panop .mul [.var .local (ofString "i"),.const 8]]) (.var .local (ofString "value"))) with
      | mk r mid =>
        rw [st] at run
        cases r with
        | none =>
          simp only at run
          exact absurd (congrArg Prod.fst run) (return_not_none mid _)
        | some r => simp at run
  · simp at run

theorem RunBounded.ite_cases {F : Type} {s : PanSemStateFiniteExact 64 F} {condition : ExpHOL 64} {yes no : ProgHOL 64}
    {cost : Nat} (a : RunBounded s yes cost) (b : RunBounded s no cost) :
    RunBounded s (.ite condition yes no) cost := by
  unfold RunBounded at *
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact b
    · exact a
  · exact ⟨Nat.le_add_right _ _,le_refl _,by simp⟩

theorem ite_normal_cases {F : Type} (s next : PanSemStateFiniteExact 64 F) (condition : ExpHOL 64) (yes no : ProgHOL 64)
    (run : evaluateHOLFiniteState s (.ite condition yes no) = (none,next)) :
    evaluateHOLFiniteState s yes = (none,next) ∨ evaluateHOLFiniteState s no = (none,next) := by
  rw [evaluateHOLFiniteState_ite] at run
  split at run
  · split at run
    · exact Or.inr run
    · exact Or.inl run
  · simp at run

#print axioms htabSetUpdate_normal

theorem insertCallCost_mono (keyLength a b : BitVec 64) (le : a.toNat ≤ b.toNat) :
    insertCallCost keyLength a ≤ insertCallCost keyLength b := by
  unfold insertCallCost; omega

/-- From an aligned table with room and word key/value locals, the trailing
insertion call and return cost at most the insertion call cost. -/
theorem runBounded_insert_tail {F : Type} (g : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count key value : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits g)
    (tL : g.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyL : g.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueL : g.locals.lookup (ofString "value") = some (.val (.word value)))
    (room : count.toNat < capacity.toNat) (small : keyLength.toNat ≤ 33806089496)
    (budget : insertCallCost keyLength capacity ≤ g.clock) :
    RunBounded g (.seq (.call (some (none,none)) (ofString "htab_insert_raw")
        [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")])
      (.return (.const 0))) (insertCallCost keyLength capacity + 0) := by
  have args : evalListHOLFinite g (h := fun a => Classical.propDecidable (g.memaddrs a))
      [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")] =
        some [.val (.word table),.val (.word key),.val (.word value)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,tL,keyL,valueL]
  obtain ⟨empty,emptyInside,emptyRead⟩ := hashOccupiedCount_exists_empty capacity (hashOccupancyRead g used)
    (by rw [← inv.agreement]; exact room)
  refine RunBounded.seq ?_ (by omega) ?_
  · exact runBounded_htabInsertRaw_call g none _ _ _ table key value capacity keyLength stride keys used empty bits
      inv.code args (inv.header_domain 16 (by omega) (by omega)) inv.cell16
      (inv.header_domain 0 (by omega) (by omega)) inv.cell0 (inv.header_domain 8 (by omega) (by omega)) inv.cell8
      (inv.header_domain 32 (by omega) (by omega)) inv.cell32 (inv.header_domain 48 (by omega) (by omega)) inv.cell48
      inv.power emptyInside (by unfold hashOccupancyRead at emptyRead; exact emptyRead) small (by unfold insertCallCost at budget; omega)
  · intro next _ nextCode _
    exact RunBounded.ofProg (ProgBounded.straight _ (by decide)) (nextCode.trans inv.code) (Nat.zero_le _)

#print axioms runBounded_insert_tail

/-- Cost of the original set body: lookup, the existing-key update (free),
growth when the load factor would exceed one half, and one insertion into the
possibly doubled table. -/
def setBodyCost (keyLength capacity count : BitVec 64) : Nat :=
  (keyLength.toNat / 8 + 8 + 1 + (capacity.toNat * (4 * keyLength.toNat + 1 + 0 + 1) + 0)) + 1 +
    (0 + (growBodyCost keyLength capacity count + 1 + (insertCallCost keyLength (capacity * 2) + 0)))

/-- The original `htab_set` body on an aligned table with count < capacity and
a heap pointer suitable for growth spends at most setBodyCost ticks in every
outcome. -/
theorem evaluate_htabSet_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count key value pointer : BitVec 64) (bits : Nat)
    (inv : HtabAligned keyLength table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerAligned : pointer.toNat % 8 = 0) (headerBelow : table.toNat + 72 ≤ pointer.toNat)
    (pointerInside : pointer.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → table.toNat ≤ a.toNat → a.toNat < 33806089496 → state.memaddrs a)
    (room : count.toNat < capacity.toNat) (small : keyLength.toNat ≤ 33806089496)
    (budget : setBodyCost keyLength capacity count ≤ state.clock) :
    RunBounded state (sourceFunctionBody Guest.guestFn_htab_set) (setBodyCost keyLength capacity count) := by
  unfold setBodyCost at budget ⊢
  rw [source_htabSet_body]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,tableLocal,keyLocal]
  refine RunBounded.decCall args budget ?_
  intro body locals returnShape lookup
  have installed : state.code.lookup (ofString "htab_find_slot") =
      some ([(ofString "t",.one),(ofString "key",.one)],sourceFunctionBody Guest.guestFn_htab_find_slot,.one) := by
    rw [inv.code]; exact originalRuntimeCode_hashFind_lookup
  rw [pan_two_word_lookup state.code.lookup (ofString "htab_find_slot") (ofString "t") (ofString "key")
    (sourceFunctionBody Guest.guestFn_htab_find_slot) table key (by decide) installed] at lookup
  cases lookup
  generalize hentry : callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update (ofString "key",.val (.word key))) = entry
  have entryFacts : entry.memory = state.memory ∧ entry.memaddrs = state.memaddrs ∧ entry.be = state.be ∧
      entry.code = state.code ∧ entry.globals = state.globals ∧ entry.clock = state.clock - 1 := by
    rw [← hentry]; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  have entryInv := inv.transfer entryFacts.1 entryFacts.2.1 entryFacts.2.2.1 entryFacts.2.2.2.1
  obtain ⟨empty,emptyInside,emptyRead⟩ := hashOccupiedCount_exists_empty capacity (hashOccupancyRead entry used)
    (by rw [← entryInv.agreement]; exact room)
  constructor
  · exact evaluate_htabFindSlot_body_bounded entry entryInv.code table key capacity keyLength stride keys used empty bits
      (by rw [← hentry]; simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      (by rw [← hentry]; simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      (entryInv.header_domain 16 (by omega) (by omega)) entryInv.cell16 (entryInv.header_domain 0 (by omega) (by omega))
      entryInv.cell0 (entryInv.header_domain 8 (by omega) (by omega)) entryInv.cell8
      (entryInv.header_domain 32 (by omega) (by omega)) entryInv.cell32 (entryInv.header_domain 48 (by omega) (by omega))
      entryInv.cell48 entryInv.power emptyInside (by unfold hashOccupancyRead at emptyRead; exact emptyRead) small
      (by rw [entryFacts.2.2.2.2.2]; omega)
  · intro v post run tc
    have frame := htabFindSlot_memoryFrame entry entryInv.code
    have meta' := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_htab_find_slot)
    rw [run] at frame meta'
    generalize hr : setVarHOLFinite (ofString "i") v { post with locals := state.locals } = r
    have rFacts : r.memory = state.memory ∧ r.memaddrs = state.memaddrs ∧ r.be = state.be ∧ r.code = state.code ∧
        r.globals = state.globals ∧ r.clock = post.clock := by
      rw [← hr]
      exact ⟨frame.1.trans entryFacts.1,meta'.2.1.trans entryFacts.2.1,meta'.2.2.1.trans entryFacts.2.2.1,
        meta'.1.trans entryFacts.2.2.2.1,frame.2.trans entryFacts.2.2.2.2.1,rfl⟩
    have rLocal : ∀ k, k ≠ ofString "i" → r.locals.lookup k = state.locals.lookup k := by
      intro k ne; rw [← hr]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne]
    have rInv := inv.transfer rFacts.1 rFacts.2.1 rFacts.2.2.1 rFacts.2.2.2.1
    have rT := (rLocal _ (by decide)).trans tableLocal
    have rKey := (rLocal _ (by decide)).trans keyLocal
    have rValue := (rLocal _ (by decide)).trans valueLocal
    refine RunBounded.seq (RunBounded.ofProg (ProgBounded.straight _ htabSetUpdate_straight) rInv.code (Nat.zero_le _))
      (by omega) ?_
    intro next upd _ _
    have same := htabSetUpdate_normal r next upd
    subst same
    have growArgs : evalListHOLFinite next (h := fun a => Classical.propDecidable (next.memaddrs a))
        [.var .local (ofString "t")] = some [.val (.word table)] := by
      rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,rT]
    refine RunBounded.seq (RunBounded.ite_cases
      (runBounded_htabGrow_call next _ keyLength table keys stride capacity used values order orderPos count pointer bits
        rInv growArgs (by rw [rFacts.2.2.2.2.1]; exact heap) pointerAligned headerBelow pointerInside
        (fun a h1 h2 h3 => by rw [rFacts.2.1]; exact arena a h1 h2 h3) room small (by omega))
      (by unfold RunBounded; rw [evaluateHOLFiniteState_skip]; exact ⟨Nat.le_add_right _ _,le_refl _,by simp⟩))
      (by omega) ?_
    intro g guardRun gCode gBudget
    have capDouble : (capacity * 2).toNat = capacity.toNat * 2 :=
      BitVec.toNat_mul_of_lt (by
        have := inv.usedBefore; have := inv.orderBefore; have := inv.endBound; change capacity.toNat * 2 < 2 ^ 64; omega)
    rcases ite_normal_cases next g _ _ _ guardRun with grown | skipped
    · obtain ⟨⟨k',u',v',o',op',gInv⟩,gLocals,_,_⟩ := htabGrow_call_normal_aligned next g _ keyLength table keys stride
        capacity used values order orderPos count pointer bits rInv growArgs (by rw [rFacts.2.2.2.2.1]; exact heap)
        pointerAligned headerBelow pointerInside (fun a h1 h2 h3 => by rw [rFacts.2.1]; exact arena a h1 h2 h3) room small
        (by omega) grown
      exact runBounded_insert_tail g keyLength table k' stride (capacity * 2) u' v' o' op' count key value (bits + 1) gInv
        (by rw [gLocals]; exact rT) (by rw [gLocals]; exact rKey) (by rw [gLocals]; exact rValue)
        (by rw [capDouble]; omega) small (by omega)
    · rw [evaluateHOLFiniteState_skip] at skipped
      obtain ⟨_,rfl⟩ := Prod.mk.inj skipped
      have doubled : capacity.toNat ≤ (capacity * 2).toNat := by rw [capDouble]; omega
      exact RunBounded.weaken (runBounded_insert_tail next keyLength table keys stride capacity used values order orderPos
        count key value bits rInv rT rKey rValue room small
        (by have := insertCallCost_mono keyLength capacity (capacity * 2) doubled; omega))
        (by have := insertCallCost_mono keyLength capacity (capacity * 2) doubled; omega)

#print axioms evaluate_htabSet_body_bounded
end InitECandidate.Runtime
