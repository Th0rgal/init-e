import InitECandidate.Runtime.HtabInsertRawFrame
import InitECandidate.Runtime.FrameHalt
import InitECandidate.Runtime.SourceByteStore
import InitECandidate.Runtime.MemzeroSyntax
import InitECandidate.Runtime.OriginalMemzeroCode
import InitECandidate.Runtime.MemzeroAlignedSuffix
import InitECandidate.Runtime.LocalBoundLoop
import InitECandidate.Runtime.PanDiscardNormalBodyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A word store that finishes normally wrote its evaluated word at its
evaluated, mapped address and nothing else. -/
theorem store_word_normal {F : Type} (state post : PanSemStateFiniteExact 64 F) (destination expression : ExpHOL 64)
    (address value : BitVec 64)
    (hAddress : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) destination = some (.val (.word address)))
    (hValue : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) expression = some (.val (.word value)))
    (run : evaluateHOLFiniteState state (.store destination expression) = (none,post)) :
    post = sourceWriteWord state address value := by
  by_cases domain : state.memaddrs address
  · rw [evaluate_store_word state address value destination expression hAddress hValue domain] at run
    cases run
    rfl
  · classical
    rw [evaluateHOLFiniteState_store,hAddress,hValue] at run
    simp [flattenHOL,panMemStoresHOL,panMemStoreHOL,domain] at run

/-- A byte store that finishes normally rewrote only the aligned cell of its address. -/
theorem storeByte_normal {F : Type} (state post : PanSemStateFiniteExact 64 F) (destination expression : ExpHOL 64)
    (address value : BitVec 64)
    (hAddress : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) destination = some (.val (.word address)))
    (hValue : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) expression = some (.val (.word value)))
    (run : evaluateHOLFiniteState state (.storeByte destination expression) = (none,post)) :
    ∃ cell, post = sourceWriteByte state address value cell := by
  obtain ⟨cell,hcell⟩ : ∃ cell, state.memory (panByteAlignHOL address) = .word cell := by
    cases h : state.memory (panByteAlignHOL address) with
    | word x => exact ⟨x,rfl⟩
  by_cases domain : state.memaddrs (panByteAlignHOL address)
  · rw [evaluate_source_storeByte state destination expression address value cell hAddress hValue domain hcell] at run
    cases run
    exact ⟨cell,rfl⟩
  · rw [evaluateHOLFiniteState_storeByte,hAddress,hValue] at run
    simp [panMemStoreByteWord8HOL,domain] at run

/-- Zeroing loop bodies: zero word/byte stores at `dst + i (+ c)` inside the
next `stride` bytes, ending with `i = i + stride`. -/
inductive ZeroStoreStep (stride : Nat) : ProgHOL 64 → Prop
  | advance : ZeroStoreStep stride (memzeroAdvance (BitVec.ofNat 64 stride))
  | wordBase {rest : ProgHOL 64} (fits : 8 ≤ stride) (tail : ZeroStoreStep stride rest) :
      ZeroStoreStep stride (.seq (.store memzeroBase (.const 0)) rest)
  | wordOffset (c : BitVec 64) {rest : ProgHOL 64} (fits : c.toNat + 8 ≤ stride) (tail : ZeroStoreStep stride rest) :
      ZeroStoreStep stride (.seq (.store (memzeroOffset c) (.const 0)) rest)
  | byteBase {rest : ProgHOL 64} (fits : 1 ≤ stride) (tail : ZeroStoreStep stride rest) :
      ZeroStoreStep stride (.seq (.storeByte memzeroBase (.const 0)) rest)
  | byteOffset (c : BitVec 64) {rest : ProgHOL 64} (fits : c.toNat + 1 ≤ stride) (tail : ZeroStoreStep stride rest) :
      ZeroStoreStep stride (.seq (.storeByte (memzeroOffset c) (.const 0)) rest)


theorem eval_const_word {F : Type} (state : PanSemStateFiniteExact 64 F) (k : BitVec 64) :
    @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) (.const k) =
      some (.val (.word k)) := by
  simp [evalHOLExact]

/-- A normally finishing zeroing body advances the counter by its stride, keeps
every other local and all metadata, and changes memory only at the word or
aligned byte cells of `dst + i + c` for c below the stride. -/
theorem ZeroStoreStep.normal_frame {stride : Nat} {body : ProgHOL 64} (step : ZeroStoreStep stride body)
    {F : Type} (s post : PanSemStateFiniteExact 64 F) (destination index : BitVec 64)
    (dstLocal : s.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (indexLocal : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (run : evaluateHOLFiniteState s body = (none,post)) :
    post.locals.lookup (ofString "i") = some (.val (.word (index + BitVec.ofNat 64 stride))) ∧
      (∀ k, k ≠ ofString "i" → post.locals.lookup k = s.locals.lookup k) ∧
      post.memaddrs = s.memaddrs ∧ post.be = s.be ∧ post.code = s.code ∧ post.clock = s.clock ∧
      post.globals = s.globals ∧
      ∀ watched : BitVec 64, (∀ c : BitVec 64, c.toNat < stride →
          watched ≠ destination + index + c ∧ watched ≠ panByteAlignHOL (destination + index + c)) →
        post.memory watched = s.memory watched := by
  induction step generalizing s with
  | advance =>
    rw [evaluate_memzero_advance s index _ indexLocal] at run
    cases run
    refine ⟨by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],
      fun k ne => by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne],
      rfl,rfl,rfl,rfl,rfl,fun _ _ => rfl⟩
  | wordBase fits tail ih =>
    rw [evaluateHOLFiniteState_seq_line780] at run
    cases first : evaluateHOLFiniteState s (.store memzeroBase (.const 0)) with
    | mk r mid =>
      rw [first] at run
      cases r with
      | some r => simp at run
      | none =>
        have written := store_word_normal s mid _ _ _ _ (eval_memzeroBase s destination index dstLocal indexLocal)
          (eval_const_word s 0) first
        subst written
        dsimp only at run
        obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8⟩ := ih _ (by exact dstLocal) (by exact indexLocal) run
        refine ⟨a1,a2,a3,a4,a5,a6,a7,fun watched cond => ?_⟩
        rw [a8 watched cond]
        have ne : watched ≠ destination + index := by simpa using (cond 0 (by simp; omega)).1
        simp [sourceWriteWord,ne]
  | wordOffset c fits tail ih =>
    rw [evaluateHOLFiniteState_seq_line780] at run
    cases first : evaluateHOLFiniteState s (.store (memzeroOffset c) (.const 0)) with
    | mk r mid =>
      rw [first] at run
      cases r with
      | some r => simp at run
      | none =>
        have written := store_word_normal s mid _ _ _ _ (eval_memzeroOffset s destination index c dstLocal indexLocal)
          (eval_const_word s 0) first
        subst written
        dsimp only at run
        obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8⟩ := ih _ (by exact dstLocal) (by exact indexLocal) run
        refine ⟨a1,a2,a3,a4,a5,a6,a7,fun watched cond => ?_⟩
        rw [a8 watched cond]
        have ne := (cond c (by omega)).1
        simp [sourceWriteWord,ne]
  | byteBase fits tail ih =>
    rw [evaluateHOLFiniteState_seq_line780] at run
    cases first : evaluateHOLFiniteState s (.storeByte memzeroBase (.const 0)) with
    | mk r mid =>
      rw [first] at run
      cases r with
      | some r => simp at run
      | none =>
        obtain ⟨cell,written⟩ := storeByte_normal s mid _ _ _ _ (eval_memzeroBase s destination index dstLocal indexLocal)
          (eval_const_word s 0) first
        subst written
        dsimp only at run
        obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8⟩ := ih _ (by exact dstLocal) (by exact indexLocal) run
        refine ⟨a1,a2,a3,a4,a5,a6,a7,fun watched cond => ?_⟩
        rw [a8 watched cond]
        have ne : watched ≠ panByteAlignHOL (destination + index) := by simpa using (cond 0 (by simp; omega)).2
        exact sourceWriteByte_memory_other s _ _ cell watched ne
  | byteOffset c fits tail ih =>
    rw [evaluateHOLFiniteState_seq_line780] at run
    cases first : evaluateHOLFiniteState s (.storeByte (memzeroOffset c) (.const 0)) with
    | mk r mid =>
      rw [first] at run
      cases r with
      | some r => simp at run
      | none =>
        obtain ⟨cell,written⟩ := storeByte_normal s mid _ _ _ _ (eval_memzeroOffset s destination index c dstLocal indexLocal)
          (eval_const_word s 0) first
        subst written
        dsimp only at run
        obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8⟩ := ih _ (by exact dstLocal) (by exact indexLocal) run
        refine ⟨a1,a2,a3,a4,a5,a6,a7,fun watched cond => ?_⟩
        rw [a8 watched cond]
        have ne := (cond c (by omega)).2
        exact sourceWriteByte_memory_other s _ _ cell watched ne

#print axioms ZeroStoreStep.normal_frame

theorem memzeroWord32Body_zero : ZeroStoreStep 32 memzeroWord32Body :=
  .wordBase (by omega) (.wordOffset 8 (by decide) (.wordOffset 16 (by decide) (.wordOffset 24 (by decide) .advance)))
theorem memzeroWord8Body_zero : ZeroStoreStep 8 memzeroWord8Body := .wordBase (by omega) .advance
theorem memzeroByte1Body_zero : ZeroStoreStep 1 memzeroByte1Body := .byteBase (by omega) .advance
theorem memzeroByte8Body_zero : ZeroStoreStep 8 memzeroByte8Body := by
  unfold memzeroByte8Body
  exact .byteBase (by omega) (.byteOffset 1 (by decide) (.byteOffset 2 (by decide) (.byteOffset 3 (by decide)
    (.byteOffset 4 (by decide) (.byteOffset 5 (by decide) (.byteOffset 6 (by decide) (.byteOffset 7 (by decide) .advance)))))))

/-- Normal loop exit with the guard available to each iteration: an invariant
kept by every normal or `continue` iteration started under a nonzero condition
holds at a normal exit, provided the body never breaks. -/
theorem while_normal_exit_guarded (condition : ExpHOL 64) (body : ProgHOL 64)
    (Inv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (keeps : ∀ {F : Type} (s post : PanSemStateFiniteExact 64 F) (w : BitVec 64), Inv s →
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) condition = some (.val (.word w)) → w ≠ 0 →
      (evaluateHOLFiniteState (decClockHOLFinite s) body = (none,post) ∨
        evaluateHOLFiniteState (decClockHOLFinite s) body = (some .continue,post)) → Inv post)
    (noBreak : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState s body).1 ≠ some .break) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.clock = n → Inv state →
      ∀ post, evaluateHOLFiniteState state (.while condition body) = (none,post) → Inv post := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F state clock invariant post run
    rw [evaluateHOLFiniteState_while_total] at run
    split at run
    · rename_i w hw
      split at run
      · rename_i nonzero
        split at run
        · simp at run
        · dsimp only at run
          rw [fixClockHOLFinite_evaluateState] at run
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          have broke := noBreak (decClockHOLFinite state)
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk r mid =>
            rw [bodyRun] at run remaining broke
            have smaller : mid.clock < n := by
              change mid.clock ≤ state.clock - 1 at remaining
              omega
            cases r with
            | none =>
              exact ih mid.clock (by omega) mid rfl (keeps state mid w invariant hw nonzero (Or.inl bodyRun)) post run
            | some r =>
              cases r with
              | «continue» =>
                exact ih mid.clock (by omega) mid rfl (keeps state mid w invariant hw nonzero (Or.inr bodyRun)) post run
              | «break» => exact absurd rfl broke
              | _ => simp at run
      · simp only [Prod.mk.injEq] at run
        obtain ⟨_,rfl⟩ := run
        exact invariant
    · simp at run

theorem seq_not_break_of_first {F : Type} (s : PanSemStateFiniteExact 64 F) (a b : ProgHOL 64)
    (first : (evaluateHOLFiniteState s a).1 = none ∨ (evaluateHOLFiniteState s a).1 = some .error)
    (rest : ∀ t : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState t b).1 ≠ some .break) :
    (evaluateHOLFiniteState s (.seq a b)).1 ≠ some .break := by
  rw [evaluateHOLFiniteState_seq_line780]
  cases h : evaluateHOLFiniteState s a with
  | mk r mid =>
    rw [h] at first
    rcases first with e | e <;> simp only at e <;> subst e
    · exact rest mid
    · simp

theorem ZeroStoreStep.not_break {stride : Nat} {body : ProgHOL 64} (step : ZeroStoreStep stride body)
    {F : Type} (s : PanSemStateFiniteExact 64 F) : (evaluateHOLFiniteState s body).1 ≠ some .break := by
  induction step generalizing s with
  | advance =>
    unfold memzeroAdvance
    rw [evaluateHOLFiniteState_assign]
    split <;> (try split) <;> simp
  | wordBase _ _ ih => exact seq_not_break_of_first s _ _ (evaluate_store_control_frame s _ _).1 ih
  | wordOffset _ _ _ ih => exact seq_not_break_of_first s _ _ (evaluate_store_control_frame s _ _).1 ih
  | byteBase _ _ ih => exact seq_not_break_of_first s _ _ (evaluate_storeByte_control_frame s _ _).1 ih
  | byteOffset _ _ _ ih => exact seq_not_break_of_first s _ _ (evaluate_storeByte_control_frame s _ _).1 ih

theorem seq_not_continue_of_first {F : Type} (s : PanSemStateFiniteExact 64 F) (a b : ProgHOL 64)
    (first : (evaluateHOLFiniteState s a).1 = none ∨ (evaluateHOLFiniteState s a).1 = some .error)
    (rest : ∀ t : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState t b).1 ≠ some .continue) :
    (evaluateHOLFiniteState s (.seq a b)).1 ≠ some .continue := by
  rw [evaluateHOLFiniteState_seq_line780]
  cases h : evaluateHOLFiniteState s a with
  | mk r mid =>
    rw [h] at first
    rcases first with e | e <;> simp only at e <;> subst e
    · exact rest mid
    · simp

theorem ZeroStoreStep.not_continue {stride : Nat} {body : ProgHOL 64} (step : ZeroStoreStep stride body)
    {F : Type} (s : PanSemStateFiniteExact 64 F) : (evaluateHOLFiniteState s body).1 ≠ some .continue := by
  induction step generalizing s with
  | advance =>
    unfold memzeroAdvance
    rw [evaluateHOLFiniteState_assign]
    split <;> (try split) <;> simp
  | wordBase _ _ ih => exact seq_not_continue_of_first s _ _ (evaluate_store_control_frame s _ _).1 ih
  | wordOffset _ _ _ ih => exact seq_not_continue_of_first s _ _ (evaluate_store_control_frame s _ _).1 ih
  | byteBase _ _ ih => exact seq_not_continue_of_first s _ _ (evaluate_storeByte_control_frame s _ _).1 ih
  | byteOffset _ _ _ ih => exact seq_not_continue_of_first s _ _ (evaluate_storeByte_control_frame s _ _).1 ih

theorem offset_address_normal (D I c : BitVec 64) (fits : I.toNat + c.toNat < 2 ^ 64) :
    D + I + c = D + BitVec.ofNat 64 (I.toNat + c.toNat) := by
  rw [BitVec.add_assoc]
  congr 1

/-- A normal exit of an original zeroing loop changes no memory cell outside
the aligned zeroed range [dst, dst + n), keeps dst/n and every other local
except the counter, and leaves the counter a word at most n. -/
theorem zeroLoop_normal_frame {stride : Nat} {body : ProgHOL 64} (step : ZeroStoreStep stride body)
    (condition : ExpHOL 64)
    (guard : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (I N w : BitVec 64),
      s.locals.lookup (ofString "i") = some (.val (.word I)) → s.locals.lookup (ofString "n") = some (.val (.word N)) →
      I.toNat ≤ N.toNat → N.toNat < 2 ^ 62 →
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) condition = some (.val (.word w)) →
      w ≠ 0 → I.toNat + stride ≤ N.toNat)
    {F : Type} (state post : PanSemStateFiniteExact 64 F) (D N watched I0 : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word D)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word N)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word I0)))
    (within : I0.toNat ≤ N.toNat)
    (aligned : D.toNat % 8 = 0) (small : D.toNat + N.toNat ≤ 33806089496)
    (outside : watched.toNat < D.toNat ∨ D.toNat + N.toNat ≤ watched.toNat)
    (run : evaluateHOLFiniteState state (.while condition body) = (none,post)) :
    post.memory watched = state.memory watched ∧
      (∀ k, k ≠ ofString "i" → post.locals.lookup k = state.locals.lookup k) ∧
      (∃ I : BitVec 64, post.locals.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat ≤ N.toNat) ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ post.code = state.code ∧ post.globals = state.globals := by
  have exit := while_normal_exit_guarded condition body
    (fun {G} (s : PanSemStateFiniteExact 64 G) => s.memory watched = state.memory watched ∧
      (∀ k, k ≠ ofString "i" → s.locals.lookup k = state.locals.lookup k) ∧
      (∃ I : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat ≤ N.toNat) ∧
      s.memaddrs = state.memaddrs ∧ s.be = state.be ∧ s.code = state.code ∧ s.globals = state.globals)
    (by
      intro G s next w ⟨sm,sl,⟨I,iL,iLe⟩,sa,sb,sc,sg⟩ cond nonzero flow
      have dL : s.locals.lookup (ofString "dst") = some (.val (.word D)) := (sl _ (by decide)).trans dstLocal
      have nL : s.locals.lookup (ofString "n") = some (.val (.word N)) := (sl _ (by decide)).trans sizeLocal
      have adv := guard s I N w iL nL iLe (by omega) cond nonzero
      rcases flow with normal | cont
      · obtain ⟨f1,f2,f3,f4,f5,f6,f7,f8⟩ := step.normal_frame (decClockHOLFinite s) next D I (by exact dL) (by exact iL) normal
        have strideSmall : stride < 2 ^ 64 := by omega
        have stepNat : (I + BitVec.ofNat 64 stride).toNat = I.toNat + stride := by
          rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt strideSmall]; omega),
            BitVec.toNat_ofNat,Nat.mod_eq_of_lt strideSmall]
        refine ⟨?_,fun k ne => (f2 k ne).trans (sl k ne),⟨I + BitVec.ofNat 64 stride,f1,by rw [stepNat]; exact adv⟩,
          f3.trans sa,f4.trans sb,f5.trans sc,f7.trans sg⟩
        rw [f8 watched ?_]
        · exact sm
        · intro c hc
          have separated := memcpy_interval_separate D N watched aligned small outside (I.toNat + c.toNat) (by omega)
          rw [offset_address_normal D I c (by omega)]
          exact separated
      · exact absurd (congrArg Prod.fst cont) (step.not_continue (decClockHOLFinite s)))
    (fun s => step.not_break s)
  exact exit state.clock state rfl ⟨rfl,fun _ _ => rfl,⟨I0,indexLocal,within⟩,rfl,rfl,rfl,rfl⟩ post run

theorem seq_result_of_first {F : Type} (s : PanSemStateFiniteExact 64 F) (a b : ProgHOL 64)
    (first : (evaluateHOLFiniteState s a).1 = none ∨ (evaluateHOLFiniteState s a).1 = some .error)
    (rest : ∀ t : PanSemStateFiniteExact 64 F,
      (evaluateHOLFiniteState t b).1 = none ∨ (evaluateHOLFiniteState t b).1 = some .error) :
    (evaluateHOLFiniteState s (.seq a b)).1 = none ∨ (evaluateHOLFiniteState s (.seq a b)).1 = some .error := by
  rw [evaluateHOLFiniteState_seq_line780]
  cases h : evaluateHOLFiniteState s a with
  | mk r mid =>
    rw [h] at first
    rcases first with e | e <;> simp only at e <;> subst e
    · exact rest mid
    · simp

theorem ZeroStoreStep.result_cases {stride : Nat} {body : ProgHOL 64} (step : ZeroStoreStep stride body)
    {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s body).1 = none ∨ (evaluateHOLFiniteState s body).1 = some .error := by
  induction step generalizing s with
  | advance =>
    unfold memzeroAdvance
    rw [evaluateHOLFiniteState_assign]
    split <;> (try split) <;> simp
  | wordBase _ _ ih => exact seq_result_of_first s _ _ (evaluate_store_control_frame s _ _).1 ih
  | wordOffset _ _ _ ih => exact seq_result_of_first s _ _ (evaluate_store_control_frame s _ _).1 ih
  | byteBase _ _ ih => exact seq_result_of_first s _ _ (evaluate_storeByte_control_frame s _ _).1 ih
  | byteOffset _ _ _ ih => exact seq_result_of_first s _ _ (evaluate_storeByte_control_frame s _ _).1 ih

/-- An original zeroing loop never returns. -/
theorem zeroLoop_not_returned {stride : Nat} {body : ProgHOL 64} (step : ZeroStoreStep stride body)
    (condition : ExpHOL 64) {F : Type} (s post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (run : evaluateHOLFiniteState s (.while condition body) = (some (.returned v),post)) : False :=
  while_returned_invariant condition body (fun _ => True) (fun _ => False) (fun _ _ => trivial)
    (fun t w q _ r => by
      rcases step.result_cases t with e | e <;> rw [r] at e <;> simp at e)
    (fun _ _ _ _ => trivial) s.clock s rfl trivial v post run

theorem memzero_block_guard (stride : BitVec 64) (small : stride.toNat ≤ 32) {F : Type} (s : PanSemStateFiniteExact 64 F)
    (I N w : BitVec 64) (iL : s.locals.lookup (ofString "i") = some (.val (.word I)))
    (nL : s.locals.lookup (ofString "n") = some (.val (.word N))) (le : I.toNat ≤ N.toNat) (bound : N.toNat < 2 ^ 62)
    (cond : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) (memzeroBlockCondition stride) =
      some (.val (.word w))) (nonzero : w ≠ 0) : I.toNat + stride.toNat ≤ N.toNat := by
  rw [show memzeroBlockCondition stride = .cmp .notLower (.var .local (ofString "n"))
      (.op .add [.var .local (ofString "i"),.const stride]) from rfl,
    eval_localBound_notLowerAdd s (ofString "i") (ofString "n") I N stride (by omega) iL nL] at cond
  by_cases fitsIn : I.toNat + stride.toNat ≤ N.toNat
  · exact fitsIn
  · simp [fitsIn] at cond; exact absurd cond.symm nonzero

theorem memzero_byte_guard {F : Type} (s : PanSemStateFiniteExact 64 F)
    (I N w : BitVec 64) (iL : s.locals.lookup (ofString "i") = some (.val (.word I)))
    (nL : s.locals.lookup (ofString "n") = some (.val (.word N))) (le : I.toNat ≤ N.toNat) (bound : N.toNat < 2 ^ 62)
    (cond : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) = some (.val (.word w)))
    (nonzero : w ≠ 0) : I.toNat + 1 ≤ N.toNat := by
  rw [eval_localBound_less s (ofString "i") (ofString "n") .lower (Or.inr rfl) I N (by omega) (by omega) iL nL] at cond
  by_cases lt : I.toNat < N.toNat
  · omega
  · simp [lt] at cond; exact absurd cond.symm nonzero

#print axioms zeroLoop_normal_frame
#print axioms while_normal_exit_guarded
#print axioms ZeroStoreStep.not_break

/-- The zeroing-stage invariant: memory at the watched cell, dst/n, and the
counter as a word at most n. -/
def ZeroStage {F : Type} (s : PanSemStateFiniteExact 64 F) (state : PanSemStateFiniteExact 64 F)
    (D N watched : BitVec 64) : Prop :=
  s.memory watched = state.memory watched ∧
    s.locals.lookup (ofString "dst") = some (.val (.word D)) ∧ s.locals.lookup (ofString "n") = some (.val (.word N)) ∧
    (∃ I : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word I)) ∧ I.toNat ≤ N.toNat)

theorem ZeroStage.loop {stride : Nat} {body : ProgHOL 64} (step : ZeroStoreStep stride body) (condition : ExpHOL 64)
    (guard : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (I N w : BitVec 64),
      s.locals.lookup (ofString "i") = some (.val (.word I)) → s.locals.lookup (ofString "n") = some (.val (.word N)) →
      I.toNat ≤ N.toNat → N.toNat < 2 ^ 62 →
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) condition = some (.val (.word w)) →
      w ≠ 0 → I.toNat + stride ≤ N.toNat)
    {F : Type} {s state post : PanSemStateFiniteExact 64 F} {D N watched : BitVec 64}
    (stage : ZeroStage s state D N watched) (aligned : D.toNat % 8 = 0) (small : D.toNat + N.toNat ≤ 33806089496)
    (outside : watched.toNat < D.toNat ∨ D.toNat + N.toNat ≤ watched.toNat)
    (run : evaluateHOLFiniteState s (.while condition body) = (none,post)) : ZeroStage post state D N watched := by
  obtain ⟨sm,dL,nL,I,iL,iLe⟩ := stage
  obtain ⟨f1,f2,f3,_⟩ := zeroLoop_normal_frame step condition guard s post D N watched I dL nL iL iLe aligned small outside run
  exact ⟨f1.trans sm,(f2 _ (by decide)).trans dL,(f2 _ (by decide)).trans nL,f3⟩

/-- A returned original memzero body changes no memory cell outside the
aligned zeroed range [dst, dst + n). -/
theorem memzero_body_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F) (D N watched : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word D)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word N)))
    (aligned : D.toNat % 8 = 0) (small : D.toNat + N.toNat ≤ 33806089496)
    (outside : watched.toNat < D.toNat ∨ D.toNat + N.toNat ≤ watched.toNat) (v : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_memzero) = (some (.returned v),post)) :
    post.memory watched = state.memory watched := by
  rw [source_memzero_body] at run
  obtain ⟨zero,i1,e1,r1,m1,_,_,_⟩ := dec_returned_state run
  rw [eval_const_word] at e1
  cases e1
  have stage0 : ZeroStage (setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state) state D N watched :=
    ⟨rfl,by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,dstLocal],
      by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,sizeLocal],0,
      by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],by simp⟩
  rw [evaluateHOLFiniteState_seq_line780] at r1
  cases alignRun : evaluateHOLFiniteState (setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state)
      (.ite (.cmp .equal (.op .and [.var .local (ofString "dst"),.const 7]) (.const 0))
        (.seq (.while (memzeroBlockCondition 32) memzeroWord32Body)
          (.while (memzeroBlockCondition 8) memzeroWord8Body)) .skip) with
  | mk ar a =>
    rw [alignRun] at r1
    -- the alignment branch only finishes normally or with an error
    have alignStage : ar = none → ZeroStage a state D N watched := by
      intro normal
      subst normal
      rw [evaluateHOLFiniteState_ite] at alignRun
      split at alignRun
      · split at alignRun
        all_goals first
          | (rw [evaluateHOLFiniteState_skip] at alignRun
             obtain ⟨_,rfl⟩ := Prod.mk.inj alignRun
             exact stage0)
          | (rw [evaluateHOLFiniteState_seq_line780] at alignRun
             cases w32 : evaluateHOLFiniteState (setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state)
                 (.while (memzeroBlockCondition 32) memzeroWord32Body) with
             | mk r b =>
               rw [w32] at alignRun
               cases r with
               | some r => simp at alignRun
               | none =>
                 simp only at alignRun
                 have stage32 := ZeroStage.loop memzeroWord32Body_zero _
                   (fun s I N w a b c d e f => memzero_block_guard 32 (by decide) s I N w a b c d e f)
                   stage0 aligned small outside w32
                 exact ZeroStage.loop memzeroWord8Body_zero _
                   (fun s I N w a b c d e f => memzero_block_guard 8 (by decide) s I N w a b c d e f)
                   stage32 aligned small outside alignRun)
      · simp at alignRun
    cases ar with
    | some r =>
      exfalso
      simp only at r1
      obtain ⟨er,_⟩ := Prod.mk.inj r1
      simp only [Option.some.injEq] at er
      subst er
      rw [evaluateHOLFiniteState_ite] at alignRun
      split at alignRun
      · split at alignRun
        all_goals first
          | (rw [evaluateHOLFiniteState_skip] at alignRun; simp at alignRun)
          | (rw [evaluateHOLFiniteState_seq_line780] at alignRun
             cases w32 : evaluateHOLFiniteState (setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state)
                 (.while (memzeroBlockCondition 32) memzeroWord32Body) with
             | mk r b =>
               rw [w32] at alignRun
               cases r with
               | none =>
                 simp only at alignRun
                 exact zeroLoop_not_returned memzeroWord8Body_zero _ b a v alignRun
               | some r =>
                 simp only at alignRun
                 obtain ⟨er,eb⟩ := Prod.mk.inj alignRun
                 simp only [Option.some.injEq] at er
                 subst er eb
                 exact zeroLoop_not_returned memzeroWord32Body_zero _ _ _ v w32)
      · simp at alignRun
    | none =>
      have stageA := alignStage rfl
      simp only at r1
      rw [evaluateHOLFiniteState_seq_line780,memzeroByte8Loop_shape] at r1
      cases b8 : evaluateHOLFiniteState a (.while (memzeroBlockCondition 8) memzeroByte8Body) with
      | mk br b =>
        rw [b8] at r1
        cases br with
        | some r =>
          exfalso
          simp only at r1
          obtain ⟨er,_⟩ := Prod.mk.inj r1
          simp only [Option.some.injEq] at er
          subst er
          exact zeroLoop_not_returned memzeroByte8Body_zero _ _ _ v b8
        | none =>
          simp only at r1
          have stageB := ZeroStage.loop memzeroByte8Body_zero _
            (fun s I N w a b c d e f => memzero_block_guard 8 (by decide) s I N w a b c d e f)
            stageA aligned small outside b8
          rw [evaluateHOLFiniteState_seq_line780] at r1
          cases b1 : evaluateHOLFiniteState b
              (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) memzeroByte1Body) with
          | mk cr c =>
            rw [b1] at r1
            cases cr with
            | some r =>
              exfalso
              simp only at r1
              obtain ⟨er,_⟩ := Prod.mk.inj r1
              simp only [Option.some.injEq] at er
              subst er
              exact zeroLoop_not_returned memzeroByte1Body_zero _ _ _ v b1
            | none =>
              simp only at r1
              have stageC := ZeroStage.loop memzeroByte1Body_zero _
                (fun s I N w a b c d e f => memzero_byte_guard s I N w a b c d e f)
                stageB aligned small outside b1
              rw [evaluateHOLFiniteState_return] at r1
              simp only [eval_const_word] at r1
              repeat' (first | (split at r1) | skip)
              all_goals (try simp only [Prod.mk.injEq] at r1)
              all_goals (try obtain ⟨_,rfl⟩ := r1)
              all_goals first
                | (rw [m1]; exact stageC.1)
                | (simp at r1)

#print axioms memzero_body_returned_memory

/-- A normally finishing original memzero call changes no memory cell outside
the aligned zeroed range [dst, dst + n), with no address-domain premise. -/
theorem memzero_call_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (D N watched : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word D),.val (.word N)])
    (code : state.code = originalRuntimeCode)
    (aligned : D.toNat % 8 = 0) (small : D.toNat + N.toNat ≤ 33806089496)
    (outside : watched.toNat < D.toNat ∨ D.toNat + N.toNat ≤ watched.toNat)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "memzero") arguments) = (none,post)) :
    post.memory watched = state.memory watched ∧ post.locals = state.locals := by
  have installed : state.code.lookup (ofString "memzero") =
      some ([(ofString "dst",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_memzero,.one) := by
    rw [code]; exact originalRuntimeCode_memzero_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "memzero") (ofString "dst") (ofString "n")
    (sourceFunctionBody Guest.guestFn_memzero) D N (by decide) installed
  obtain ⟨value,output,bodyRun,memory,locals⟩ := evaluate_discard_normal_body_memory state post (ofString "memzero")
    arguments [.val (.word D),.val (.word N)] (sourceFunctionBody Guest.guestFn_memzero) _ .one args lookup run
  refine ⟨?_,locals⟩
  rw [memory]
  exact memzero_body_returned_memory (callEntryStateHOLFinite state
      ((HolFiniteMapExact.empty.update (ofString "dst",.val (.word D))).update (ofString "n",.val (.word N))))
    output D N watched
    (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    aligned small outside value bodyRun

#print axioms memzero_call_normal_memory
end InitECandidate.Runtime
