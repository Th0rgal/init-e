import InitECandidate.Runtime.HtabSetBound
import InitECandidate.Runtime.VmFn_mpt_fail
import InitECandidate.Runtime.TrieWalkNullBound
import InitECandidate.Runtime.KeyToNibblesSyntax
import InitECandidate.Runtime.ByteStoreMemoryFrame
import InitECandidate.Runtime.ByteStoreChainFrame
import InitECandidate.Runtime.KeyToNibblesStepFrame
import InitECandidate.Runtime.OriginalKeyToNibblesCode
import InitECandidate.Runtime.OriginalTrieWalkCode
import InitECandidate.Runtime.OriginalTrieLookupCode
import InitECandidate.Runtime.PanThreeWordLookup
import InitECandidate.Runtime.GlobalsFrameComposition
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A discarded call of an installed function whose body keeps memory and globals keeps them too, in every
outcome (argument or lookup failure, timeout, exception, return). -/
theorem memoryFrame_discardCall (function : MlS) (arguments : List (ExpHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (bodyFrame : MemoryFrame body) : MemoryFrame (.call (some (none,none)) function arguments) := by
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
      · have frame := bodyFrame (callEntryStateHOLFinite state callee) code
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at frame
          obtain ⟨fm,fg⟩ := frame
          change bodyPost.memory = state.memory at fm
          change bodyPost.globals = state.globals at fg
          rcases rb with _ | (_ | _ | _ | _ | w | _ | _)
          all_goals (dsimp only; try split)
          all_goals exact ⟨fm,fg⟩

#print axioms memoryFrame_discardCall

theorem mptFail_memoryFrame : MemoryFrame (sourceFunctionBody Guest.guestFn_mpt_fail) :=
  memoryFrame_leaf _ (by simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]; rfl)

/-- Memory-and-globals frame tactic over the constructs used by the MPT read path. -/
syntax "mem_frame" : tactic
macro_rules
  | `(tactic| mem_frame) => `(tactic| repeat first
      | exact memoryFrame_leaf _ (by decide)
      | apply memoryFrame_seq
      | apply memoryFrame_dec
      | apply memoryFrame_ite
      | apply memoryFrame_while
      | apply memoryFrame_decCall _ _ _ _ _ _ _ originalRuntimeCode_memeq_lookup (memoryFrame_leaf _ memeq_readOnlyMemory)
      | exact memoryFrame_discardCall _ _ _ _ _ vmLookup_mpt_fail mptFail_memoryFrame)

set_option maxHeartbeats 4000000 in
/-- The original `trie_walk` keeps memory and globals in every outcome: normal return, the `MptErr` raised through
`mpt_fail` on a hashed node, invalid reads and timeouts. -/
theorem trieWalk_memoryFrame : MemoryFrame (sourceFunctionBody Guest.guestFn_trie_walk) := by
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  mem_frame

#print axioms trieWalk_memoryFrame

/-- A tail call (`return f(args)`) of an installed function whose body keeps memory and globals keeps them too, in
every outcome. -/
theorem memoryFrame_tailCall (function : MlS) (arguments : List (ExpHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (bodyFrame : MemoryFrame body) : MemoryFrame (.call none function arguments) := by
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
      · have frame := bodyFrame (callEntryStateHOLFinite state callee) code
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at frame
          obtain ⟨fm,fg⟩ := frame
          change bodyPost.memory = state.memory at fm
          change bodyPost.globals = state.globals at fg
          rcases rb with _ | (_ | _ | _ | _ | w | _ | _)
          all_goals (dsimp only; try split)
          all_goals exact ⟨fm,fg⟩

#print axioms memoryFrame_tailCall

/-- A discarded call whose looked-up body keeps a watched word and the globals from the actual callee entry state
keeps them, in every outcome. -/
theorem watch_discardCall {F : Type} (state : PanSemStateFiniteExact 64 F) (w : BitVec 64) (function : MlS)
    (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments = some values)
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (bodyWatch : (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2.memory w = state.memory w ∧
      (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2.globals = state.globals) :
    (evaluateHOLFiniteState state (.call (some (none,none)) function arguments)).2.memory w = state.memory w ∧
      (evaluateHOLFiniteState state (.call (some (none,none)) function arguments)).2.globals = state.globals := by
  rw [evaluateHOLFiniteState_call,args]
  dsimp only
  rw [lookup]
  dsimp only
  split
  · simp [emptyLocalsHOLFinite]
  · cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
    | mk rb bodyPost =>
      rw [bodyRun] at bodyWatch
      obtain ⟨fm,fg⟩ := bodyWatch
      change bodyPost.memory w = state.memory w at fm
      change bodyPost.globals = state.globals at fg
      rcases rb with _ | (_ | _ | _ | _ | v | _ | _)
      all_goals (dsimp only; try split)
      all_goals exact ⟨fm,fg⟩

#print axioms watch_discardCall

/-- Byte-store straight-line code whose stores all avoid a watched word, from any state whose locals satisfy `G`
(stable under the code's own local declarations). -/
inductive WinStep (G : HolFiniteMapExact MlS (ValueHOL 64) → Prop) (watched : BitVec 64) : ProgHOL 64 → Prop
  | tail (program : ProgHOL 64) (supported : readOnlyMemory program = true) : WinStep G watched program
  | store (destination value : ExpHOL 64) {rest : ProgHOL 64}
      (target : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), G s.locals → ∃ address : BitVec 64,
        @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) destination =
          some (.val (.word address)) ∧ watched ≠ panByteAlignHOL address)
      (next : WinStep G watched rest) : WinStep G watched (.seq (.storeByte destination value) rest)
  | declare (name : MlS) (initializer : ExpHOL 64) {body : ProgHOL 64}
      (stable : ∀ L v, G L → G (L.update (name,v))) (nested : WinStep G watched body) :
      WinStep G watched (.dec name .one initializer body)


theorem evaluate_winStep {G : HolFiniteMapExact MlS (ValueHOL 64) → Prop} {w : BitVec 64} {program : ProgHOL 64}
    (h : WinStep G w program) : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), G s.locals →
      (evaluateHOLFiniteState s program).2.memory w = s.memory w := by
  induction h with
  | tail p ro => intro F s _; exact congrFun (evaluate_readOnly_memory p ro s) w
  | store d v target _ ih =>
    intro F s g
    obtain ⟨a,ev,ne⟩ := target s g
    have frame := evaluate_storeByte_memory_frame s d v a w ev ne
    have control := evaluate_storeByte_control_frame s d v
    rw [evaluateHOLFiniteState_seq_line780]
    cases stored : evaluateHOLFiniteState s (.storeByte d v) with
    | mk r m =>
      rw [stored] at frame control
      dsimp only at frame control
      rcases control.1 with rfl | rfl
      · exact (ih m (by rw [control.2.2.1]; exact g)).trans frame
      · exact frame
  | declare name init stable _ ih =>
    intro F s g
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · rfl
    · split
      · exact ih _ (stable _ _ g)
      · rfl

#print axioms evaluate_winStep

theorem eval_nibDest {F : Type} (s : PanSemStateFiniteExact 64 F) (I O c : BitVec 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word I)))
    (ho : s.locals.lookup (ofString "out") = some (.val (.word O))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "out"),.panop .mul [.const 2,.var .local (ofString "i")],.const c]) =
      some (.val (.word (O + 2 * I + c))) := by
  simp [evalHOLExact,evalListHOLExact,hi,ho,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]
  exact (BitVec.add_assoc _ _ _).symm

theorem eval_nibDest0 {F : Type} (s : PanSemStateFiniteExact 64 F) (I O : BitVec 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word I)))
    (ho : s.locals.lookup (ofString "out") = some (.val (.word O))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "out"),.panop .mul [.const 2,.var .local (ofString "i")]]) =
      some (.val (.word (O + 2 * I + 0))) := by
  simp [evalHOLExact,evalListHOLExact,hi,ho,wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL]

def nibG (I O : BitVec 64) (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  L.lookup (ofString "i") = some (.val (.word I)) ∧ L.lookup (ofString "out") = some (.val (.word O))

set_option maxHeartbeats 4000000 in
theorem keyToNibbles_main_winStep (I O w : BitVec 64)
    (hw : ∀ c : Nat, c < 8 → w ≠ panByteAlignHOL (O + 2 * I + BitVec.ofNat 64 c)) :
    WinStep (nibG I O) w keyToNibblesMainStep := by
  simp only [keyToNibblesMainStep,keyToNibblesMainLoop,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  repeat first
    | exact WinStep.tail _ (by decide)
    | refine WinStep.store _ _ (fun s h => ⟨_,eval_nibDest s I O _ h.1 h.2,hw _ (by decide)⟩) ?_
    | refine WinStep.store _ _ (fun s h => ⟨_,eval_nibDest0 s I O h.1 h.2,hw 0 (by decide)⟩) ?_
    | refine WinStep.declare _ _ (fun L v h => ⟨by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,h.1],
        by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,h.2]⟩) ?_

set_option maxHeartbeats 4000000 in
theorem keyToNibbles_tail_winStep (I O w : BitVec 64)
    (hw : ∀ c : Nat, c < 2 → w ≠ panByteAlignHOL (O + 2 * I + BitVec.ofNat 64 c)) :
    WinStep (nibG I O) w keyToNibblesTailStep := by
  simp only [keyToNibblesTailStep,keyToNibblesTailLoop,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  repeat first
    | exact WinStep.tail _ (by decide)
    | refine WinStep.store _ _ (fun s h => ⟨_,eval_nibDest s I O _ h.1 h.2,hw _ (by decide)⟩) ?_
    | refine WinStep.store _ _ (fun s h => ⟨_,eval_nibDest0 s I O h.1 h.2,hw 0 (by decide)⟩) ?_
    | refine WinStep.declare _ _ (fun L v h => ⟨by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,h.1],
        by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,h.2]⟩) ?_

#print axioms keyToNibbles_main_winStep
#print axioms keyToNibbles_tail_winStep

/-- A loop keeps a watched word in every outcome if each iteration entered with a nonzero condition keeps it and
re-establishes an invariant on normal, `continue` or `break` exit; a normal loop exit satisfies the invariant. -/
theorem evaluate_while_watch {F : Type} (condition : ExpHOL 64) (body : ProgHOL 64) (w : BitVec 64)
    (Inv : PanSemStateFiniteExact 64 F → Prop)
    (step : ∀ s : PanSemStateFiniteExact 64 F, Inv s → ∀ v : BitVec 64,
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) condition = some (.val (.word v)) → v ≠ 0 →
      (evaluateHOLFiniteState (decClockHOLFinite s) body).2.memory w = s.memory w ∧
      ((evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .continue ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .break →
        Inv (evaluateHOLFiniteState (decClockHOLFinite s) body).2))
    (s : PanSemStateFiniteExact 64 F) (inv : Inv s) :
    (evaluateHOLFiniteState s (.while condition body)).2.memory w = s.memory w ∧
      ((evaluateHOLFiniteState s (.while condition body)).1 = none → Inv (evaluateHOLFiniteState s (.while condition body)).2) := by
  rw [evaluateHOLFiniteState_while_total]
  split
  · rename_i v hv
    split
    · rename_i nz
      split
      · exact ⟨rfl,fun h => by cases h⟩
      · dsimp only
        rw [fixClockHOLFinite_evaluateState]
        have st := step s inv v hv nz
        have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
        cases run : evaluateHOLFiniteState (decClockHOLFinite s) body with
        | mk result middle =>
          rw [run] at st remaining
          have smaller : middle.clock < s.clock := by
            change middle.clock ≤ s.clock - 1 at remaining
            omega
          cases result with
          | none =>
            have again := evaluate_while_watch condition body w Inv step middle (st.2 (Or.inl rfl))
            exact ⟨again.1.trans st.1,again.2⟩
          | some result =>
            cases result with
            | «continue» =>
              have again := evaluate_while_watch condition body w Inv step middle (st.2 (Or.inr (Or.inl rfl)))
              exact ⟨again.1.trans st.1,again.2⟩
            | «break» => exact ⟨st.1,fun _ => st.2 (Or.inr (Or.inr rfl))⟩
            | returned _ => exact ⟨st.1,fun h => by cases h⟩
            | exception _ _ => exact ⟨st.1,fun h => by cases h⟩
            | finalFfi _ => exact ⟨st.1,fun h => by cases h⟩
            | error => exact ⟨st.1,fun h => by cases h⟩
            | timeOut => exact ⟨st.1,fun h => by cases h⟩
    · exact ⟨rfl,fun _ => inv⟩
  · exact ⟨rfl,fun h => by cases h⟩
termination_by s.clock

#print axioms evaluate_while_watch

theorem nib_addr_eq (O I : BitVec 64) (c : Nat) (_h : 2 * I.toNat + c < 2 ^ 64) :
    O + 2 * I + BitVec.ofNat 64 c = O + BitVec.ofNat 64 (2 * I.toNat + c) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have t2 : (2 : BitVec 64).toNat = 2 := rfl
  rw [BitVec.toNat_add,BitVec.toNat_mul,t2,BitVec.toNat_ofNat,BitVec.toNat_ofNat]
  omega


def nibInv {F : Type} (O N : BitVec 64) (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.locals.lookup (ofString "out") = some (.val (.word O)) ∧ s.locals.lookup (ofString "n") = some (.val (.word N)) ∧
    ∃ I : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat ≤ N.toNat

set_option maxHeartbeats 4000000 in
/-- The original `key_to_nibbles` body writes only inside its output window: from any entry with locals `out = O`
and `n = N` (2N small), every word other than the aligned words of `[O, O + 2N)` is unchanged, in every outcome
(byte failures, timeouts and normal return). -/
theorem keyToNibbles_body_window {F : Type} (s : PanSemStateFiniteExact 64 F) (O N w : BitVec 64)
    (ho : s.locals.lookup (ofString "out") = some (.val (.word O)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word N))) (small : 2 * N.toNat + 8 < 2 ^ 64)
    (hw : ∀ j : Nat, j < 2 * N.toNat → w ≠ panByteAlignHOL (O + BitVec.ofNat 64 j)) :
    (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_key_to_nibbles)).2.memory w = s.memory w := by
  have stepM : ∀ s' : PanSemStateFiniteExact 64 F, nibInv O N s' → ∀ v : BitVec 64,
      evalHOLFinite s' (h := fun a => Classical.propDecidable (s'.memaddrs a))
        (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"),.const 4])) =
          some (.val (.word v)) → v ≠ 0 →
      (evaluateHOLFiniteState (decClockHOLFinite s') keyToNibblesMainStep).2.memory w = s'.memory w ∧
      ((evaluateHOLFiniteState (decClockHOLFinite s') keyToNibblesMainStep).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s') keyToNibblesMainStep).1 = some .continue ∨
        (evaluateHOLFiniteState (decClockHOLFinite s') keyToNibblesMainStep).1 = some .break →
        nibInv O N (evaluateHOLFiniteState (decClockHOLFinite s') keyToNibblesMainStep).2) := by
    intro s' ⟨ho',hn',I,hi',le⟩ v hv nz
    rw [evalHOLFinite_eq_toExact] at hv
    simp [evalHOLExact,evalListHOLExact,hi',hn',wordOpHOL,wordOp,valueIsWord,valueWord,
      Compiler.Encoders.Asm.wordCmpHOL] at hv
    have g : I + 4#64 ≤ N := by
      by_cases c : I + 4#64 ≤ N
      · exact c
      · simp [c] at hv; exact absurd hv.symm nz
    have i4 : (I + 4#64).toNat = I.toNat + 4 := by
      rw [BitVec.toNat_add]; have : (4#64).toNat = 4 := rfl; rw [this]; omega
    have i4' : (I + 4).toNat = I.toNat + 4 := i4
    rw [BitVec.le_def,i4] at g
    refine ⟨evaluate_winStep (keyToNibbles_main_winStep I O w (fun c hc => by
      rw [nib_addr_eq O I c (by omega)]; exact hw _ (by omega))) (decClockHOLFinite s') (by exact ⟨hi',ho'⟩),?_⟩
    obtain ⟨result,post,run,_,others,cases⟩ := evaluate_keyToNibbles_main_step_frame (decClockHOLFinite s') I hi'
    rw [run]
    intro hres
    rcases cases with ⟨rfl,hi2⟩ | rfl
    · exact ⟨(others _ (by decide)).trans ho',(others _ (by decide)).trans hn',I + 4,hi2,by rw [i4']; omega⟩
    · simp at hres
  have stepT : ∀ s' : PanSemStateFiniteExact 64 F, nibInv O N s' → ∀ v : BitVec 64,
      evalHOLFinite s' (h := fun a => Classical.propDecidable (s'.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) = some (.val (.word v)) → v ≠ 0 →
      (evaluateHOLFiniteState (decClockHOLFinite s') keyToNibblesTailStep).2.memory w = s'.memory w ∧
      ((evaluateHOLFiniteState (decClockHOLFinite s') keyToNibblesTailStep).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s') keyToNibblesTailStep).1 = some .continue ∨
        (evaluateHOLFiniteState (decClockHOLFinite s') keyToNibblesTailStep).1 = some .break →
        nibInv O N (evaluateHOLFiniteState (decClockHOLFinite s') keyToNibblesTailStep).2) := by
    intro s' ⟨ho',hn',I,hi',le⟩ v hv nz
    rw [evalHOLFinite_eq_toExact] at hv
    simp [evalHOLExact,hi',hn',Compiler.Encoders.Asm.wordCmpHOL] at hv
    have g : I < N := by
      by_cases c : I < N
      · exact c
      · simp [c] at hv; exact absurd hv.symm nz
    rw [BitVec.lt_def] at g
    refine ⟨evaluate_winStep (keyToNibbles_tail_winStep I O w (fun c hc => by
      rw [nib_addr_eq O I c (by omega)]; exact hw _ (by omega))) (decClockHOLFinite s') (by exact ⟨hi',ho'⟩),?_⟩
    obtain ⟨result,post,run,_,others,cases⟩ := evaluate_keyToNibbles_tail_step_frame (decClockHOLFinite s') I hi'
    rw [run]
    intro hres
    rcases cases with ⟨rfl,hi2⟩ | rfl
    · refine ⟨(others _ (by decide)).trans ho',(others _ (by decide)).trans hn',I + 1,hi2,?_⟩
      rw [BitVec.toNat_add]; have : (1 : BitVec 64).toNat = 1 := rfl; rw [this]; omega
    · simp at hres
  rw [source_keyToNibbles_body,evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · rfl
  · rename_i value hval
    split
    · have hv0 : value = .val (.word 0) := by simp [evalHOLExact] at hval; exact hval.symm
      subst hv0
      change (evaluateHOLFiniteState (setVarHOLFinite (ofString "i") (.val (.word 0)) s)
        (.seq keyToNibblesMainLoop (.seq keyToNibblesTailLoop (.return (.const 0))))).2.memory w = s.memory w
      have inv0 : nibInv O N (setVarHOLFinite (ofString "i") (.val (.word 0)) s) :=
        ⟨by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ho],
         by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hn],
         0,by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],by simp⟩
      have main := evaluate_while_watch _ keyToNibblesMainStep w (nibInv O N) stepM _ inv0
      rw [← source_keyToNibbles_main_loop] at main
      rw [evaluateHOLFiniteState_seq_line780]
      cases r1 : evaluateHOLFiniteState (setVarHOLFinite (ofString "i") (.val (.word 0)) s) keyToNibblesMainLoop with
      | mk res1 m1 =>
        rw [r1] at main
        cases res1 with
        | some x => exact main.1
        | none =>
          dsimp only
          have tail := evaluate_while_watch _ keyToNibblesTailStep w (nibInv O N) stepT m1 (main.2 rfl)
          rw [← source_keyToNibbles_tail_loop] at tail
          rw [evaluateHOLFiniteState_seq_line780]
          cases r2 : evaluateHOLFiniteState m1 keyToNibblesTailLoop with
          | mk res2 m2 =>
            rw [r2] at tail
            cases res2 with
            | some x => exact tail.1.trans main.1
            | none =>
              dsimp only
              rw [congrFun (evaluate_readOnly_memory (.return (.const 0)) (by decide) m2) w]
              exact tail.1.trans main.1
    · rfl

#print axioms keyToNibbles_body_window

set_option maxHeartbeats 2000000 in
/-- A discarded call `key_to_nibbles(key, n, out)` with word arguments keeps the globals and every word outside
the aligned words of `[out, out + 2n)`, in every outcome. -/
theorem keyToNibbles_call_window {F : Type} (s : PanSemStateFiniteExact 64 F) (arguments : List (ExpHOL 64))
    (K N O w : BitVec 64) (code : s.code = originalRuntimeCode)
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments =
      some [.val (.word K),.val (.word N),.val (.word O)])
    (small : 2 * N.toNat + 8 < 2 ^ 64)
    (hw : ∀ j : Nat, j < 2 * N.toNat → w ≠ panByteAlignHOL (O + BitVec.ofNat 64 j)) :
    (evaluateHOLFiniteState s (.call (some (none,none)) (ofString "key_to_nibbles") arguments)).2.memory w = s.memory w ∧
      (evaluateHOLFiniteState s (.call (some (none,none)) (ofString "key_to_nibbles") arguments)).2.globals =
        s.globals := by
  have lookup := pan_three_word_lookup s.code.lookup (ofString "key_to_nibbles") (ofString "key") (ofString "n")
    (ofString "out") (sourceFunctionBody Guest.guestFn_key_to_nibbles) K N O (by decide) (by decide) (by decide)
    (by rw [code]; exact originalRuntimeCode_keyToNibbles_lookup)
  refine watch_discardCall s w _ _ _ args _ _ _ lookup ⟨?_,?_⟩
  · exact keyToNibbles_body_window _ O N w
      (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      small hw
  · exact originalGlobalsFrame_leaf _ (fun _ => by
      simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]; rfl) _ code

#print axioms keyToNibbles_call_window

def trieLookupBody : ProgHOL 64 :=
  .seq (.call (some (none,none)) (ofString "key_to_nibbles")
      [.var .local (ofString "key_hash32"),.const 32,.var .global (ofString "mpt_nib_scratch")])
    (.call none (ofString "trie_walk")
      [.var .local (ofString "root"),.var .global (ofString "mpt_nib_scratch"),.const 64])

theorem source_trieLookup_body : sourceFunctionBody Guest.guestFn_trie_lookup = trieLookupBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

set_option maxHeartbeats 2000000 in
/-- The original `trie_lookup(root, key_hash32)` body keeps the globals and every word outside the 64-byte nibble
scratch buffer `mpt_nib_scratch`, in every outcome (nibble conversion failures, `MptErr` from `trie_walk` on a
hashed node, timeouts, and the normal return). -/
theorem trieLookup_body_window {F : Type} (s : PanSemStateFiniteExact 64 F) (H NB w : BitVec 64)
    (code : s.code = originalRuntimeCode)
    (hH : s.locals.lookup (ofString "key_hash32") = some (.val (.word H)))
    (hNB : s.globals.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (hw : ∀ j : Nat, j < 64 → w ≠ panByteAlignHOL (NB + BitVec.ofNat 64 j)) :
    (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_trie_lookup)).2.memory w = s.memory w ∧
      (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_trie_lookup)).2.globals = s.globals := by
  rw [source_trieLookup_body]
  unfold trieLookupBody
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "key_hash32"),.const 32,.var .global (ofString "mpt_nib_scratch")] =
      some [.val (.word H),.val (.word 32),.val (.word NB)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,hH,hNB]
  have first := keyToNibbles_call_window s _ H 32 NB w code args (by decide) (fun j hj => hw j (by
    have : (32 : BitVec 64).toNat = 32 := rfl; omega))
  have meta' := evaluateHOLFiniteState_metadata s (.call (some (none,none)) (ofString "key_to_nibbles")
    [.var .local (ofString "key_hash32"),.const 32,.var .global (ofString "mpt_nib_scratch")])
  rw [evaluateHOLFiniteState_seq_line780]
  cases r1 : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "key_to_nibbles")
      [.var .local (ofString "key_hash32"),.const 32,.var .global (ofString "mpt_nib_scratch")]) with
  | mk res m =>
    rw [r1] at first meta'
    cases res with
    | some x => exact first
    | none =>
      dsimp only
      have tail := memoryFrame_tailCall _ [.var .local (ofString "root"),.var .global (ofString "mpt_nib_scratch"),.const 64]
        _ _ _ originalRuntimeCode_trieWalk_lookup trieWalk_memoryFrame m (meta'.1.trans code)
      exact ⟨by rw [congrFun tail.1 w]; exact first.1,tail.2.trans first.2⟩

#print axioms trieLookup_body_window
end InitECandidate.Runtime
