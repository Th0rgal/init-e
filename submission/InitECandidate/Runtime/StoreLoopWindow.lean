import InitECandidate.Runtime.MptReadFrame
import InitECandidate.Runtime.ByteStoresControlFrame
import InitECandidate.Runtime.ByteAdvanceStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A word store whose value evaluates to a single word changes memory only at its address, and only memory. -/
theorem evaluate_store_word_frame {F : Type} (s : PanSemStateFiniteExact 64 F) (d v : ExpHOL 64) (a : BitVec 64)
    (hd : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) d = some (.val (.word a)))
    (hv : ∀ x, @evalHOLExact 64 F _ s.toExact (fun y => Classical.propDecidable (s.memaddrs y)) v = some x →
      ∃ y : BitVec 64, x = .val (.word y)) :
    ((evaluateHOLFiniteState s (.store d v)).1 = none ∨ (evaluateHOLFiniteState s (.store d v)).1 = some .error) ∧
      (evaluateHOLFiniteState s (.store d v)).2.clock = s.clock ∧
      (evaluateHOLFiniteState s (.store d v)).2.locals = s.locals ∧
      (evaluateHOLFiniteState s (.store d v)).2.globals = s.globals ∧
      (∀ w : BitVec 64, w ≠ a → (evaluateHOLFiniteState s (.store d v)).2.memory w = s.memory w) := by
  rw [evaluateHOLFiniteState_store,hd]
  dsimp only
  split
  · rename_i x hx
    obtain ⟨y,rfl⟩ := hv x hx
    split
    · rename_i m hm
      simp only [flattenHOL,panMemStoresHOL,panMemStoreHOL] at hm
      split at hm
      · simp only [Option.some.injEq] at hm
        subst hm
        refine ⟨Or.inl rfl,rfl,rfl,rfl,fun w ne => ?_⟩
        rename_i upd hupd
        split at hupd
        · simp only [Option.some.injEq] at hupd
          rw [← hupd]; simp [ne]
        · cases hupd
      · cases hm
    · exact ⟨Or.inr rfl,rfl,rfl,rfl,fun _ _ => rfl⟩
  · exact ⟨Or.inr rfl,rfl,rfl,rfl,fun _ _ => rfl⟩

#print axioms evaluate_store_word_frame

/-- Every word store ends normally or with an error, and keeps clock, locals and globals. -/
theorem evaluate_store_control {F : Type} (s : PanSemStateFiniteExact 64 F) (d v : ExpHOL 64) :
    ((evaluateHOLFiniteState s (.store d v)).1 = none ∨ (evaluateHOLFiniteState s (.store d v)).1 = some .error) ∧
      (evaluateHOLFiniteState s (.store d v)).2.clock = s.clock ∧
      (evaluateHOLFiniteState s (.store d v)).2.locals = s.locals ∧
      (evaluateHOLFiniteState s (.store d v)).2.globals = s.globals := by
  rw [evaluateHOLFiniteState_store]
  split
  · split
    · split
      · exact ⟨Or.inl rfl,rfl,rfl,rfl⟩
      · exact ⟨Or.inr rfl,rfl,rfl,rfl⟩
    · exact ⟨Or.inr rfl,rfl,rfl,rfl⟩
  · exact ⟨Or.inr rfl,rfl,rfl,rfl⟩

/-- Straight-line byte and word stores, local declarations and a read-only tail, with every store avoiding a
watched word from states whose locals satisfy `G`. -/
inductive WStep (G : HolFiniteMapExact MlS (ValueHOL 64) → Prop) (watched : BitVec 64) : ProgHOL 64 → Prop
  | tail (program : ProgHOL 64) (supported : readOnlyMemory program = true) : WStep G watched program
  | byte (destination value : ExpHOL 64) {rest : ProgHOL 64}
      (target : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), G s.locals → ∃ address : BitVec 64,
        @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) destination =
          some (.val (.word address)) ∧ watched ≠ panByteAlignHOL address)
      (next : WStep G watched rest) : WStep G watched (.seq (.storeByte destination value) rest)
  | word (destination value : ExpHOL 64) {rest : ProgHOL 64}
      (target : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), G s.locals → ∃ address : BitVec 64,
        @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) destination =
          some (.val (.word address)) ∧ watched ≠ address)
      (isWord : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x,
        @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) value = some x →
          ∃ y : BitVec 64, x = .val (.word y))
      (next : WStep G watched rest) : WStep G watched (.seq (.store destination value) rest)
  | declare (name : MlS) (initializer : ExpHOL 64) {body : ProgHOL 64}
      (stable : ∀ L v, G L → G (L.update (name,v))) (nested : WStep G watched body) :
      WStep G watched (.dec name .one initializer body)

theorem evaluate_wStep {G : HolFiniteMapExact MlS (ValueHOL 64) → Prop} {w : BitVec 64} {program : ProgHOL 64}
    (h : WStep G w program) : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), G s.locals →
      (evaluateHOLFiniteState s program).2.memory w = s.memory w := by
  induction h with
  | tail p ro => intro F s _; exact congrFun (evaluate_readOnly_memory p ro s) w
  | byte d v target _ ih =>
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
  | word d v target isWord _ ih =>
    intro F s g
    obtain ⟨a,ev,ne⟩ := target s g
    have facts := evaluate_store_word_frame s d v a ev (isWord s)
    rw [evaluateHOLFiniteState_seq_line780]
    cases stored : evaluateHOLFiniteState s (.store d v) with
    | mk r m =>
      rw [stored] at facts
      dsimp only at facts
      obtain ⟨control,_,loc,_,mem⟩ := facts
      rcases control with rfl | rfl
      · exact (ih m (by rw [loc]; exact g)).trans (mem w ne)
      · exact mem w ne
  | declare name init stable _ ih =>
    intro F s g
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · rfl
    · split
      · exact ih _ (stable _ _ g)
      · rfl

#print axioms evaluate_wStep

/-- Straight-line byte and word stores and declarations ending in `counter := counter + increment`. -/
inductive AdvStep (counter : MlS) (increment : BitVec 64) : ProgHOL 64 → Prop
  | advance : AdvStep counter increment (.assign .local counter (.op .add [.var .local counter,.const increment]))
  | byte (destination value : ExpHOL 64) {rest : ProgHOL 64} (tail : AdvStep counter increment rest) :
      AdvStep counter increment (.seq (.storeByte destination value) rest)
  | word (destination value : ExpHOL 64) {rest : ProgHOL 64} (tail : AdvStep counter increment rest) :
      AdvStep counter increment (.seq (.store destination value) rest)
  | declare (name : MlS) (initializer : ExpHOL 64) {body : ProgHOL 64}
      (different : name ≠ counter) (nested : AdvStep counter increment body) :
      AdvStep counter increment (.dec name .one initializer body)

/-- Normal completion advances the counter exactly; every outcome keeps all other locals and is normal or an error. -/
theorem evaluate_advStep {F : Type} {counter : MlS} {increment : BitVec 64} {program : ProgHOL 64}
    (supported : AdvStep counter increment program) (state : PanSemStateFiniteExact 64 F)
    (index : BitVec 64) (binding : state.locals.lookup counter = some (.val (.word index))) :
    ∃ result post, evaluateHOLFiniteState state program = (result,post) ∧
      (∀ name, name ≠ counter → post.locals.lookup name = state.locals.lookup name) ∧
      ((result = none ∧ post.locals.lookup counter = some (.val (.word (index + increment)))) ∨ result = some .error) := by
  induction supported generalizing state with
  | advance =>
    refine ⟨none,setVarHOLFinite counter (.val (.word (index + increment))) state,?_,?_,Or.inl ⟨rfl,?_⟩⟩
    · simp [evaluateHOLFiniteState_assign,evalHOLExact,evalListHOLExact,binding,wordOpHOL,wordOp,valueIsWord,valueWord,lookupKvarHOLExact,isValidValueHOLExact,setKvarHOLFinite,shapeOfHOLExact,shapeEqHOL]
    · intro name different
      simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
    · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  | byte destination value tail ih =>
    have facts := evaluate_storeByte_control_frame state destination value
    cases stored : evaluateHOLFiniteState state (.storeByte destination value) with
    | mk result middle =>
      rw [stored] at facts
      dsimp only at facts
      obtain ⟨control,_,locals,_,_,_,_⟩ := facts
      rcases control with rfl | rfl
      · obtain ⟨result,post,run,frame,normal⟩ := ih middle (by rw [locals]; exact binding)
        refine ⟨result,post,?_,?_,normal⟩
        · rw [evaluateHOLFiniteState_seq_line780,stored]; exact run
        · intro name different; rw [frame name different,locals]
      · refine ⟨some .error,middle,?_,?_,Or.inr rfl⟩
        · rw [evaluateHOLFiniteState_seq_line780,stored]
        · intro name _; rw [locals]
  | word destination value tail ih =>
    have facts := evaluate_store_control state destination value
    cases stored : evaluateHOLFiniteState state (.store destination value) with
    | mk result middle =>
      rw [stored] at facts
      dsimp only at facts
      obtain ⟨control,_,locals,_⟩ := facts
      rcases control with rfl | rfl
      · obtain ⟨result,post,run,frame,normal⟩ := ih middle (by rw [locals]; exact binding)
        refine ⟨result,post,?_,?_,normal⟩
        · rw [evaluateHOLFiniteState_seq_line780,stored]; exact run
        · intro name different; rw [frame name different,locals]
      · refine ⟨some .error,middle,?_,?_,Or.inr rfl⟩
        · rw [evaluateHOLFiniteState_seq_line780,stored]
        · intro name _; rw [locals]
  | declare name initializer different nested ih =>
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · exact ⟨some .error,state,rfl,(by intro _ _; rfl),Or.inr rfl⟩
    · rename_i value initialized
      split
      · have childBinding : (setVarHOLFinite name value state).locals.lookup counter = some (.val (.word index)) := by
          simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different] using binding
        obtain ⟨result,post,run,frame,normal⟩ := ih (setVarHOLFinite name value state) childBinding
        rw [run]
        refine ⟨result,_,rfl,?_,?_⟩
        · intro key other
          cases saved : state.locals.lookup name
          all_goals
            by_cases same : key = name
            · subst key; simp [saved,FDOMSUB_HOL,FUPDATE_HOL]
            · simp [FDOMSUB_HOL,FUPDATE_HOL,same,Ne.symm same,frame key other,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
        · rcases normal with ⟨rfl,advanced⟩ | rfl
          · left; refine ⟨rfl,?_⟩
            cases saved : state.locals.lookup name <;>
              simpa [lookup_resVarEq_toExact,resVarHOLExact,saved,FDOMSUB_HOL,FUPDATE_HOL,different,Ne.symm different] using advanced
          · exact Or.inr rfl
      · exact ⟨some .error,state,rfl,(by intro _ _; rfl),Or.inr rfl⟩

#print axioms evaluate_advStep

def LoopInv {F : Type} (P : HolFiniteMapExact MlS (ValueHOL 64) → Prop) (counter : MlS) (Q : BitVec 64 → Prop)
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  P s.locals ∧ ∃ I : BitVec 64, s.locals.lookup counter = some (.val (.word I)) ∧ Q I

/-- A counted store loop keeps a watched word in every outcome: each iteration entered with a nonzero condition
advances the counter, keeps the other locals (so `P`), re-establishes `Q`, and its stores avoid the watched word. -/
theorem storeLoop_watch {F : Type} (condition : ExpHOL 64) (step : ProgHOL 64) (counter : MlS) (inc w : BitVec 64)
    (P : HolFiniteMapExact MlS (ValueHOL 64) → Prop) (Q : BitVec 64 → Prop) (adv : AdvStep counter inc step)
    (pStable : ∀ L L' : HolFiniteMapExact MlS (ValueHOL 64), P L →
      (∀ name, name ≠ counter → L'.lookup name = L.lookup name) → P L')
    (iter : ∀ (s : PanSemStateFiniteExact 64 F) (I v : BitVec 64), P s.locals →
      s.locals.lookup counter = some (.val (.word I)) → Q I →
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) condition = some (.val (.word v)) → v ≠ 0 →
      Q (I + inc) ∧ WStep (fun L => P L ∧ L.lookup counter = some (.val (.word I))) w step)
    (s : PanSemStateFiniteExact 64 F) (inv : LoopInv P counter Q s) :
    (evaluateHOLFiniteState s (.while condition step)).2.memory w = s.memory w ∧
      ((evaluateHOLFiniteState s (.while condition step)).1 = none →
        LoopInv P counter Q (evaluateHOLFiniteState s (.while condition step)).2) := by
  refine evaluate_while_watch condition step w (LoopInv P counter Q) ?_ s inv
  intro s' ⟨p,I,hi,q⟩ v hv nz
  obtain ⟨qn,ws⟩ := iter s' I v p hi q hv nz
  refine ⟨evaluate_wStep ws (decClockHOLFinite s') (by exact ⟨p,hi⟩),?_⟩
  obtain ⟨result,post,run,frame,normal⟩ := evaluate_advStep adv (decClockHOLFinite s') I hi
  rw [run]
  intro hres
  rcases normal with ⟨rfl,adv'⟩ | rfl
  · exact ⟨pStable _ _ p (fun name ne => frame name ne),I + inc,adv',qn⟩
  · simp at hres

#print axioms storeLoop_watch

theorem cond_notLower {F : Type} (s : PanSemStateFiniteExact 64 F) (I N k v : BitVec 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word I)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word N)))
    (hv : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"),.const k])) =
        some (.val (.word v))) (nz : v ≠ 0) (le : I.toNat ≤ N.toNat) (small : N.toNat + k.toNat < 2 ^ 64) :
    I.toNat + k.toNat ≤ N.toNat := by
  rw [evalHOLFinite_eq_toExact] at hv
  simp [evalHOLExact,evalListHOLExact,hi,hn,wordOpHOL,wordOp,valueIsWord,valueWord,
    Compiler.Encoders.Asm.wordCmpHOL] at hv
  have g : I + k ≤ N := by
    by_cases c : I + k ≤ N
    · exact c
    · simp [c] at hv; exact absurd hv.symm nz
  rw [BitVec.le_def,BitVec.toNat_add,Nat.mod_eq_of_lt (by omega)] at g
  exact g

theorem cond_lower {F : Type} (s : PanSemStateFiniteExact 64 F) (I N v : BitVec 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word I)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word N)))
    (hv : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) = some (.val (.word v)))
    (nz : v ≠ 0) : I.toNat < N.toNat := by
  rw [evalHOLFinite_eq_toExact] at hv
  simp [evalHOLExact,hi,hn,Compiler.Encoders.Asm.wordCmpHOL] at hv
  have g : I < N := by
    by_cases c : I < N
    · exact c
    · simp [c] at hv; exact absurd hv.symm nz
  exact BitVec.lt_def.mp g

#print axioms cond_notLower
#print axioms cond_lower

theorem addr_add_eq (D I c : BitVec 64) : D + I + c = D + BitVec.ofNat 64 (I.toNat + c.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
  omega

theorem eval_addr2 {F : Type} (s : PanSemStateFiniteExact 64 F) (base : MlS) (D I : BitVec 64)
    (hd : s.locals.lookup base = some (.val (.word D)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word I))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local base,.var .local (ofString "i")]) = some (.val (.word (D + I + 0))) := by
  simp [evalHOLExact,evalListHOLExact,hd,hi,wordOpHOL,wordOp,valueIsWord,valueWord]

theorem eval_addr3 {F : Type} (s : PanSemStateFiniteExact 64 F) (base : MlS) (D I c : BitVec 64)
    (hd : s.locals.lookup base = some (.val (.word D)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word I))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local base,.var .local (ofString "i"),.const c]) = some (.val (.word (D + I + c))) := by
  simp [evalHOLExact,evalListHOLExact,hd,hi,wordOpHOL,wordOp,valueIsWord,valueWord]
  exact (BitVec.add_assoc _ _ _).symm

theorem isWord_const {F : Type} (s : PanSemStateFiniteExact 64 F) (k : BitVec 64) (x : ValueHOL 64)
    (hx : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.const k) = some x) :
    ∃ y : BitVec 64, x = .val (.word y) := ⟨k,by simp [evalHOLExact] at hx; exact hx.symm⟩

theorem isWord_load {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) (x : ValueHOL 64)
    (hx : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.load .one e) = some x) :
    ∃ y : BitVec 64, x = .val (.word y) := by
  simp only [evalHOLExact] at hx
  split at hx
  · simp only [memLoadHOLExact] at hx
    split at hx
    · split at hx
      · injection hx with hx
        subst hx
        generalize s.memory _ = m
        cases m with
        | word y => exact ⟨y,rfl⟩
      · cases hx
    · cases hx
  · cases hx

/-- The words a store loop over `[D, D + N)` may touch: each address and its aligned word. -/
def MWin (D : BitVec 64) (N : Nat) (w : BitVec 64) : Prop :=
  ∃ j : Nat, j < N ∧ (w = D + BitVec.ofNat 64 j ∨ w = panByteAlignHOL (D + BitVec.ofNat 64 j))

theorem mwin_off {D I c w : BitVec 64} {N : Nat} (out : ¬ MWin D N w) (lt : I.toNat + c.toNat < N) :
    w ≠ D + I + c ∧ w ≠ panByteAlignHOL (D + I + c) := by
  rw [addr_add_eq]
  exact ⟨fun e => out ⟨_,lt,Or.inl e⟩,fun e => out ⟨_,lt,Or.inr e⟩⟩

/-- Window step tactic: discharges store targets of `dst + i (+ c)` from `hwin`. -/
syntax "wstep_win" ident : tactic
macro_rules
  | `(tactic| wstep_win $hwin) => `(tactic| repeat first
      | exact WStep.tail _ (by decide)
      | refine WStep.word _ _ (fun s h => ⟨_,eval_addr3 s _ _ _ _ (h.1.1) h.2,($hwin _ (by decide)).1⟩)
          (fun s x hx => isWord_const s _ x hx) ?_
      | refine WStep.word _ _ (fun s h => ⟨_,eval_addr2 s _ _ _ (h.1.1) h.2,($hwin _ (by decide)).1⟩)
          (fun s x hx => isWord_const s _ x hx) ?_
      | refine WStep.word _ _ (fun s h => ⟨_,eval_addr3 s _ _ _ _ (h.1.1) h.2,($hwin _ (by decide)).1⟩)
          (fun s x hx => isWord_load s _ x hx) ?_
      | refine WStep.word _ _ (fun s h => ⟨_,eval_addr2 s _ _ _ (h.1.1) h.2,($hwin _ (by decide)).1⟩)
          (fun s x hx => isWord_load s _ x hx) ?_
      | refine WStep.byte _ _ (fun s h => ⟨_,eval_addr3 s _ _ _ _ (h.1.1) h.2,($hwin _ (by decide)).2⟩) ?_
      | refine WStep.byte _ _ (fun s h => ⟨_,eval_addr2 s _ _ _ (h.1.1) h.2,($hwin _ (by decide)).2⟩) ?_)

def memzeroHOL : ProgHOL 64 := (.dec (ofString "i") .one (.const 0) (.seq (.ite (.cmp .equal (.op .and [(.var .local (ofString "dst")),(.const 7)]) (.const 0)) (.seq (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [(.var .local (ofString "i")),(.const 32)])) (.seq (.store (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i"))]) (.const 0)) (.seq (.store (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 8)]) (.const 0)) (.seq (.store (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 16)]) (.const 0)) (.seq (.store (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 24)]) (.const 0)) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 32)]))))))) (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [(.var .local (ofString "i")),(.const 8)])) (.seq (.store (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i"))]) (.const 0)) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 8)]))))) .skip) (.seq (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [(.var .local (ofString "i")),(.const 8)])) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i"))]) (.const 0)) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 1)]) (.const 0)) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 2)]) (.const 0)) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 3)]) (.const 0)) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 4)]) (.const 0)) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 5)]) (.const 0)) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 6)]) (.const 0)) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 7)]) (.const 0)) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 8)]))))))))))) (.seq (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i"))]) (.const 0)) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 1)])))) (.return (.const 0))))))

theorem source_memzero_hol : sourceFunctionBody Guest.guestFn_memzero = memzeroHOL := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl


/-- A store loop guarded by `i + k ≤ n` whose stores lie at `base + i + c` (c < k) keeps every word outside the
window `[D, D + N)`, with the invariant `i ≤ n`. -/
theorem notLowerLoop_window {F : Type} (step : ProgHOL 64) (k : BitVec 64) (D N w : BitVec 64)
    (P : HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (pBase : ∀ L, P L → L.lookup (ofString "n") = some (.val (.word N)))
    (pStable : ∀ L L' : HolFiniteMapExact MlS (ValueHOL 64), P L →
      (∀ name, name ≠ ofString "i" → L'.lookup name = L.lookup name) → P L')
    (adv : AdvStep (ofString "i") k step)
    (win : ∀ I : BitVec 64, (∀ c : BitVec 64, c.toNat < k.toNat → w ≠ D + I + c ∧ w ≠ panByteAlignHOL (D + I + c)) →
      WStep (fun L => P L ∧ L.lookup (ofString "i") = some (.val (.word I))) w step)
    (small : N.toNat + k.toNat < 2 ^ 64) (out : ¬ MWin D N.toNat w)
    (s : PanSemStateFiniteExact 64 F) (inv : LoopInv P (ofString "i") (fun I => I.toNat ≤ N.toNat) s) :
    (evaluateHOLFiniteState s (.while (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"),.const k])) step)).2.memory w = s.memory w ∧
      ((evaluateHOLFiniteState s (.while (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"),.const k])) step)).1 = none →
        LoopInv P (ofString "i") (fun I => I.toNat ≤ N.toNat) (evaluateHOLFiniteState s (.while (.cmp .notLower
          (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"),.const k])) step)).2) := by
  refine storeLoop_watch _ step _ k w P _ adv pStable ?_ s inv
  intro s' I v p hi q hv nz
  have g := cond_notLower s' I N k v hi (pBase _ p) hv nz q small
  refine ⟨?_,win I (fun c hc => mwin_off out (by omega))⟩
  show (I + k).toNat ≤ N.toNat
  rw [BitVec.toNat_add,Nat.mod_eq_of_lt (by omega)]; exact g

/-- A store loop guarded by `i < n` whose stores lie at `base + i` keeps every word outside `[D, D + N)`. -/
theorem lowerLoop_window {F : Type} (step : ProgHOL 64) (k : BitVec 64) (D N w : BitVec 64)
    (P : HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (pBase : ∀ L, P L → L.lookup (ofString "n") = some (.val (.word N)))
    (pStable : ∀ L L' : HolFiniteMapExact MlS (ValueHOL 64), P L →
      (∀ name, name ≠ ofString "i" → L'.lookup name = L.lookup name) → P L')
    (adv : AdvStep (ofString "i") k step)
    (win : ∀ I : BitVec 64, (∀ c : BitVec 64, c.toNat < 1 → w ≠ D + I + c ∧ w ≠ panByteAlignHOL (D + I + c)) →
      WStep (fun L => P L ∧ L.lookup (ofString "i") = some (.val (.word I))) w step)
    (out : ¬ MWin D N.toNat w)
    (s : PanSemStateFiniteExact 64 F) (inv : LoopInv P (ofString "i") (fun _ => True) s) :
    (evaluateHOLFiniteState s (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) step)).2.memory w =
      s.memory w := by
  refine (storeLoop_watch _ step _ k w P _ adv pStable ?_ s inv).1
  intro s' I v p hi _ hv nz
  have g := cond_lower s' I N v hi (pBase _ p) hv nz
  exact ⟨trivial,win I (fun c hc => mwin_off out (by omega))⟩

#print axioms notLowerLoop_window
#print axioms lowerLoop_window

def memzeroP (D N : BitVec 64) (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  L.lookup (ofString "dst") = some (.val (.word D)) ∧ L.lookup (ofString "n") = some (.val (.word N))

theorem memzeroP_stable (D N : BitVec 64) : ∀ L L' : HolFiniteMapExact MlS (ValueHOL 64), memzeroP D N L →
    (∀ name, name ≠ ofString "i" → L'.lookup name = L.lookup name) → memzeroP D N L' :=
  fun _ _ p f => ⟨(f _ (by decide)).trans p.1,(f _ (by decide)).trans p.2⟩

/-- AdvStep tactic. -/
syntax "adv_step" : tactic
macro_rules
  | `(tactic| adv_step) => `(tactic| repeat first
      | exact AdvStep.advance
      | apply AdvStep.word
      | apply AdvStep.byte
      | (apply AdvStep.declare; decide))

def memzeroL32Step : ProgHOL 64 := (.seq (.store (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i"))]) (.const 0)) (.seq (.store (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 8)]) (.const 0)) (.seq (.store (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 16)]) (.const 0)) (.seq (.store (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 24)]) (.const 0)) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 32)]))))))

def memzeroL8wStep : ProgHOL 64 := (.seq (.store (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i"))]) (.const 0)) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 8)])))

def memzeroL8bStep : ProgHOL 64 := (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i"))]) (.const 0)) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 1)]) (.const 0)) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 2)]) (.const 0)) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 3)]) (.const 0)) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 4)]) (.const 0)) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 5)]) (.const 0)) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 6)]) (.const 0)) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 7)]) (.const 0)) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 8)]))))))))))

def memzeroL1Step : ProgHOL 64 := (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i"))]) (.const 0)) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 1)])))



/-- Watched-word frames compose through `seq` with intermediate invariants. -/
theorem seq_watch {F : Type} (p q : ProgHOL 64) (w : BitVec 64) (A B C : PanSemStateFiniteExact 64 F → Prop)
    (hp : ∀ s, A s → (evaluateHOLFiniteState s p).2.memory w = s.memory w ∧
      ((evaluateHOLFiniteState s p).1 = none → B (evaluateHOLFiniteState s p).2))
    (hq : ∀ s, B s → (evaluateHOLFiniteState s q).2.memory w = s.memory w ∧
      ((evaluateHOLFiniteState s q).1 = none → C (evaluateHOLFiniteState s q).2))
    (s : PanSemStateFiniteExact 64 F) (a : A s) :
    (evaluateHOLFiniteState s (.seq p q)).2.memory w = s.memory w ∧
      ((evaluateHOLFiniteState s (.seq p q)).1 = none → C (evaluateHOLFiniteState s (.seq p q)).2) := by
  have h1 := hp s a
  rw [evaluateHOLFiniteState_seq_line780]
  cases r : evaluateHOLFiniteState s p with
  | mk res m =>
    rw [r] at h1
    cases res with
    | some x => exact ⟨h1.1,fun h => by cases h⟩
    | none =>
      have h2 := hq m (h1.2 rfl)
      exact ⟨h2.1.trans h1.1,h2.2⟩

theorem ite_watch {F : Type} (condition : ExpHOL 64) (yes no : ProgHOL 64) (w : BitVec 64)
    (A B : PanSemStateFiniteExact 64 F → Prop)
    (hy : ∀ s, A s → (evaluateHOLFiniteState s yes).2.memory w = s.memory w ∧
      ((evaluateHOLFiniteState s yes).1 = none → B (evaluateHOLFiniteState s yes).2))
    (hn : ∀ s, A s → (evaluateHOLFiniteState s no).2.memory w = s.memory w ∧
      ((evaluateHOLFiniteState s no).1 = none → B (evaluateHOLFiniteState s no).2))
    (s : PanSemStateFiniteExact 64 F) (a : A s) :
    (evaluateHOLFiniteState s (.ite condition yes no)).2.memory w = s.memory w ∧
      ((evaluateHOLFiniteState s (.ite condition yes no)).1 = none → B (evaluateHOLFiniteState s (.ite condition yes no)).2) := by
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact hn s a
    · exact hy s a
  · exact ⟨rfl,fun h => by cases h⟩

theorem skip_watch {F : Type} (w : BitVec 64) (A : PanSemStateFiniteExact 64 F → Prop) (s : PanSemStateFiniteExact 64 F)
    (a : A s) : (evaluateHOLFiniteState s .skip).2.memory w = s.memory w ∧
      ((evaluateHOLFiniteState s .skip).1 = none → A (evaluateHOLFiniteState s .skip).2) := by
  rw [evaluateHOLFiniteState_skip]; exact ⟨rfl,fun _ => a⟩

set_option maxHeartbeats 4000000 in
/-- The original `memzero(dst, n)` body writes only inside `[D, D + N)` (each address and its aligned word), in
every outcome. -/
theorem memzero_body_window {F : Type} (s : PanSemStateFiniteExact 64 F) (D N w : BitVec 64)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word D)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word N)))
    (small : N.toNat + 32 < 2 ^ 64) (out : ¬ MWin D N.toNat w) :
    (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_memzero)).2.memory w = s.memory w := by
  have e8 : (8 : BitVec 64).toNat = 8 := rfl
  have e32 : (32 : BitVec 64).toNat = 32 := rfl
  have L32 := fun (t : PanSemStateFiniteExact 64 F) (inv : LoopInv (memzeroP D N) (ofString "i") (fun I => I.toNat ≤ N.toNat) t) =>
    notLowerLoop_window memzeroL32Step 32 D N w (memzeroP D N) (fun _ p => p.2) (memzeroP_stable D N)
      (by unfold memzeroL32Step; adv_step) (fun I hwin => by unfold memzeroL32Step; wstep_win hwin)
      (by rw [e32]; exact small) out t inv
  have L8w := fun (t : PanSemStateFiniteExact 64 F) (inv : LoopInv (memzeroP D N) (ofString "i") (fun I => I.toNat ≤ N.toNat) t) =>
    notLowerLoop_window memzeroL8wStep 8 D N w (memzeroP D N) (fun _ p => p.2) (memzeroP_stable D N)
      (by unfold memzeroL8wStep; adv_step) (fun I hwin => by unfold memzeroL8wStep; wstep_win hwin)
      (by rw [e8]; omega) out t inv
  have L8b := fun (t : PanSemStateFiniteExact 64 F) (inv : LoopInv (memzeroP D N) (ofString "i") (fun I => I.toNat ≤ N.toNat) t) =>
    notLowerLoop_window memzeroL8bStep 8 D N w (memzeroP D N) (fun _ p => p.2) (memzeroP_stable D N)
      (by unfold memzeroL8bStep; adv_step) (fun I hwin => by unfold memzeroL8bStep; wstep_win hwin)
      (by rw [e8]; omega) out t inv
  have L1 := fun (t : PanSemStateFiniteExact 64 F) (inv : LoopInv (memzeroP D N) (ofString "i") (fun _ => True) t) =>
    lowerLoop_window memzeroL1Step 1 D N w (memzeroP D N) (fun _ p => p.2) (memzeroP_stable D N)
      (by unfold memzeroL1Step; adv_step) (fun I hwin => by unfold memzeroL1Step; wstep_win hwin) out t inv
  rw [source_memzero_hol]
  unfold memzeroHOL
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · rfl
  · rename_i value hval
    split
    · have hv0 : value = .val (.word 0) := by simp [evalHOLExact] at hval; exact hval.symm
      subst hv0
      have inv0 : LoopInv (memzeroP D N) (ofString "i") (fun I => I.toNat ≤ N.toNat)
          (setVarHOLFinite (ofString "i") (.val (.word 0)) s) :=
        ⟨⟨by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hd],
          by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hn]⟩,
         0,by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],by simp⟩
      change (evaluateHOLFiniteState (setVarHOLFinite (ofString "i") (.val (.word 0)) s) _).2.memory w = s.memory w
      refine (seq_watch _ _ w _ (LoopInv (memzeroP D N) (ofString "i") (fun I => I.toNat ≤ N.toNat)) (fun _ => True)
        (ite_watch _ _ _ w _ _ (seq_watch _ _ w _ _ _ L32 L8w) (skip_watch w _))
        (seq_watch _ _ w _ (LoopInv (memzeroP D N) (ofString "i") (fun I => I.toNat ≤ N.toNat)) (fun _ => True) L8b
          (seq_watch _ _ w (LoopInv (memzeroP D N) (ofString "i") (fun I => I.toNat ≤ N.toNat)) (fun _ => True) (fun _ => True)
            (fun t ⟨p,I,hi,_⟩ => ⟨L1 t ⟨p,I,hi,trivial⟩,fun _ => trivial⟩)
            (fun t _ => ⟨congrFun (evaluate_readOnly_memory (.return (.const 0)) (by decide) t) w,fun _ => trivial⟩)))
        _ inv0).1
    · rfl

#print axioms memzero_body_window

def memcpyHOL : ProgHOL 64 := (.dec (ofString "i") .one (.const 0) (.seq (.ite (.cmp .equal (.op .and [(.op .or [(.var .local (ofString "dst")),(.var .local (ofString "src"))]),(.const 7)]) (.const 0)) (.seq (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [(.var .local (ofString "i")),(.const 32)])) (.seq (.store (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i"))]) (.load .one (.op .add [(.var .local (ofString "src")),(.var .local (ofString "i"))]))) (.seq (.store (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 8)]) (.load .one (.op .add [(.var .local (ofString "src")),(.var .local (ofString "i")),(.const 8)]))) (.seq (.store (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 16)]) (.load .one (.op .add [(.var .local (ofString "src")),(.var .local (ofString "i")),(.const 16)]))) (.seq (.store (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 24)]) (.load .one (.op .add [(.var .local (ofString "src")),(.var .local (ofString "i")),(.const 24)]))) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 32)]))))))) (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [(.var .local (ofString "i")),(.const 8)])) (.seq (.store (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i"))]) (.load .one (.op .add [(.var .local (ofString "src")),(.var .local (ofString "i"))]))) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 8)]))))) .skip) (.seq (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [(.var .local (ofString "i")),(.const 8)])) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i"))]) (.loadByte (.op .add [(.var .local (ofString "src")),(.var .local (ofString "i"))]))) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 1)]) (.loadByte (.op .add [(.var .local (ofString "src")),(.var .local (ofString "i")),(.const 1)]))) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 2)]) (.loadByte (.op .add [(.var .local (ofString "src")),(.var .local (ofString "i")),(.const 2)]))) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 3)]) (.loadByte (.op .add [(.var .local (ofString "src")),(.var .local (ofString "i")),(.const 3)]))) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 4)]) (.loadByte (.op .add [(.var .local (ofString "src")),(.var .local (ofString "i")),(.const 4)]))) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 5)]) (.loadByte (.op .add [(.var .local (ofString "src")),(.var .local (ofString "i")),(.const 5)]))) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 6)]) (.loadByte (.op .add [(.var .local (ofString "src")),(.var .local (ofString "i")),(.const 6)]))) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 7)]) (.loadByte (.op .add [(.var .local (ofString "src")),(.var .local (ofString "i")),(.const 7)]))) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 8)]))))))))))) (.seq (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i"))]) (.loadByte (.op .add [(.var .local (ofString "src")),(.var .local (ofString "i"))]))) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 1)])))) (.return (.const 0))))))

theorem source_memcpy_hol : sourceFunctionBody Guest.guestFn_memcpy = memcpyHOL := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

def memcpyL32Step : ProgHOL 64 := (.seq (.store (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i"))]) (.load .one (.op .add [(.var .local (ofString "src")),(.var .local (ofString "i"))]))) (.seq (.store (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 8)]) (.load .one (.op .add [(.var .local (ofString "src")),(.var .local (ofString "i")),(.const 8)]))) (.seq (.store (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 16)]) (.load .one (.op .add [(.var .local (ofString "src")),(.var .local (ofString "i")),(.const 16)]))) (.seq (.store (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 24)]) (.load .one (.op .add [(.var .local (ofString "src")),(.var .local (ofString "i")),(.const 24)]))) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 32)]))))))

def memcpyL8wStep : ProgHOL 64 := (.seq (.store (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i"))]) (.load .one (.op .add [(.var .local (ofString "src")),(.var .local (ofString "i"))]))) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 8)])))

def memcpyL8bStep : ProgHOL 64 := (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i"))]) (.loadByte (.op .add [(.var .local (ofString "src")),(.var .local (ofString "i"))]))) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 1)]) (.loadByte (.op .add [(.var .local (ofString "src")),(.var .local (ofString "i")),(.const 1)]))) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 2)]) (.loadByte (.op .add [(.var .local (ofString "src")),(.var .local (ofString "i")),(.const 2)]))) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 3)]) (.loadByte (.op .add [(.var .local (ofString "src")),(.var .local (ofString "i")),(.const 3)]))) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 4)]) (.loadByte (.op .add [(.var .local (ofString "src")),(.var .local (ofString "i")),(.const 4)]))) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 5)]) (.loadByte (.op .add [(.var .local (ofString "src")),(.var .local (ofString "i")),(.const 5)]))) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 6)]) (.loadByte (.op .add [(.var .local (ofString "src")),(.var .local (ofString "i")),(.const 6)]))) (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i")),(.const 7)]) (.loadByte (.op .add [(.var .local (ofString "src")),(.var .local (ofString "i")),(.const 7)]))) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 8)]))))))))))

def memcpyL1Step : ProgHOL 64 := (.seq (.storeByte (.op .add [(.var .local (ofString "dst")),(.var .local (ofString "i"))]) (.loadByte (.op .add [(.var .local (ofString "src")),(.var .local (ofString "i"))]))) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 1)])))

def memcpyP (D S N : BitVec 64) (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  L.lookup (ofString "dst") = some (.val (.word D)) ∧ L.lookup (ofString "n") = some (.val (.word N)) ∧
    L.lookup (ofString "src") = some (.val (.word S))

theorem memcpyP_stable (D S N : BitVec 64) : ∀ L L' : HolFiniteMapExact MlS (ValueHOL 64), memcpyP D S N L →
    (∀ name, name ≠ ofString "i" → L'.lookup name = L.lookup name) → memcpyP D S N L' :=
  fun _ _ p f => ⟨(f _ (by decide)).trans p.1,(f _ (by decide)).trans p.2.1,(f _ (by decide)).trans p.2.2⟩

set_option maxHeartbeats 4000000 in
/-- The original `memcpy(dst, src, n)` body writes only inside `[D, D + N)` (each address and its aligned word), in
every outcome; the source is only read. -/
theorem memcpy_body_window {F : Type} (s : PanSemStateFiniteExact 64 F) (D S N w : BitVec 64)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word D)))
    (hs : s.locals.lookup (ofString "src") = some (.val (.word S)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word N)))
    (small : N.toNat + 32 < 2 ^ 64) (out : ¬ MWin D N.toNat w) :
    (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_memcpy)).2.memory w = s.memory w := by
  have e8 : (8 : BitVec 64).toNat = 8 := rfl
  have e32 : (32 : BitVec 64).toNat = 32 := rfl
  have L32 := fun (t : PanSemStateFiniteExact 64 F) (inv : LoopInv (memcpyP D S N) (ofString "i") (fun I => I.toNat ≤ N.toNat) t) =>
    notLowerLoop_window memcpyL32Step 32 D N w (memcpyP D S N) (fun _ p => p.2.1) (memcpyP_stable D S N)
      (by unfold memcpyL32Step; adv_step) (fun I hwin => by unfold memcpyL32Step; wstep_win hwin)
      (by rw [e32]; exact small) out t inv
  have L8w := fun (t : PanSemStateFiniteExact 64 F) (inv : LoopInv (memcpyP D S N) (ofString "i") (fun I => I.toNat ≤ N.toNat) t) =>
    notLowerLoop_window memcpyL8wStep 8 D N w (memcpyP D S N) (fun _ p => p.2.1) (memcpyP_stable D S N)
      (by unfold memcpyL8wStep; adv_step) (fun I hwin => by unfold memcpyL8wStep; wstep_win hwin)
      (by rw [e8]; omega) out t inv
  have L8b := fun (t : PanSemStateFiniteExact 64 F) (inv : LoopInv (memcpyP D S N) (ofString "i") (fun I => I.toNat ≤ N.toNat) t) =>
    notLowerLoop_window memcpyL8bStep 8 D N w (memcpyP D S N) (fun _ p => p.2.1) (memcpyP_stable D S N)
      (by unfold memcpyL8bStep; adv_step) (fun I hwin => by unfold memcpyL8bStep; wstep_win hwin)
      (by rw [e8]; omega) out t inv
  have L1 := fun (t : PanSemStateFiniteExact 64 F) (inv : LoopInv (memcpyP D S N) (ofString "i") (fun _ => True) t) =>
    lowerLoop_window memcpyL1Step 1 D N w (memcpyP D S N) (fun _ p => p.2.1) (memcpyP_stable D S N)
      (by unfold memcpyL1Step; adv_step) (fun I hwin => by unfold memcpyL1Step; wstep_win hwin) out t inv
  rw [source_memcpy_hol]
  unfold memcpyHOL
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · rfl
  · rename_i value hval
    split
    · have hv0 : value = .val (.word 0) := by simp [evalHOLExact] at hval; exact hval.symm
      subst hv0
      have inv0 : LoopInv (memcpyP D S N) (ofString "i") (fun I => I.toNat ≤ N.toNat)
          (setVarHOLFinite (ofString "i") (.val (.word 0)) s) :=
        ⟨⟨by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hd],
          by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hn],
          by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hs]⟩,
         0,by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],by simp⟩
      change (evaluateHOLFiniteState (setVarHOLFinite (ofString "i") (.val (.word 0)) s) _).2.memory w = s.memory w
      refine (seq_watch _ _ w _ (LoopInv (memcpyP D S N) (ofString "i") (fun I => I.toNat ≤ N.toNat)) (fun _ => True)
        (ite_watch _ _ _ w _ _ (seq_watch _ _ w _ _ _ L32 L8w) (skip_watch w _))
        (seq_watch _ _ w _ (LoopInv (memcpyP D S N) (ofString "i") (fun I => I.toNat ≤ N.toNat)) (fun _ => True) L8b
          (seq_watch _ _ w (LoopInv (memcpyP D S N) (ofString "i") (fun I => I.toNat ≤ N.toNat)) (fun _ => True) (fun _ => True)
            (fun t ⟨p,I,hi,_⟩ => ⟨L1 t ⟨p,I,hi,trivial⟩,fun _ => trivial⟩)
            (fun t _ => ⟨congrFun (evaluate_readOnly_memory (.return (.const 0)) (by decide) t) w,fun _ => trivial⟩)))
        _ inv0).1
    · rfl

#print axioms memcpy_body_window
end InitECandidate.Runtime
