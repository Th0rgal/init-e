import InitECandidate.Runtime.MemzeroNormalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Memory separation for arbitrary zeroing destinations, including unaligned
padding tails. Both direct word stores and aligned byte-store cells are covered. -/
theorem zeroLoop_normal_separated_frame {stride : Nat} {body : ProgHOL 64} (step : ZeroStoreStep stride body)
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
    (small : D.toNat + N.toNat ≤ 33806089496)
    (separate : ∀ offset : Nat, offset < N.toNat →
      watched ≠ D + BitVec.ofNat 64 offset ∧ watched ≠ panByteAlignHOL (D + BitVec.ofNat 64 offset))
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
          have separated := separate (I.toNat + c.toNat) (by omega)
          rw [offset_address_normal D I c (by omega)]
          exact separated
      · exact absurd (congrArg Prod.fst cont) (step.not_continue (decClockHOLFinite s)))
    (fun s => step.not_break s)
  exact exit state.clock state rfl ⟨rfl,fun _ _ => rfl,⟨I0,indexLocal,within⟩,rfl,rfl,rfl,rfl⟩ post run

theorem ZeroStage.separated_loop {stride : Nat} {body : ProgHOL 64} (step : ZeroStoreStep stride body) (condition : ExpHOL 64)
    (guard : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (I N w : BitVec 64),
      s.locals.lookup (ofString "i") = some (.val (.word I)) → s.locals.lookup (ofString "n") = some (.val (.word N)) →
      I.toNat ≤ N.toNat → N.toNat < 2 ^ 62 →
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) condition = some (.val (.word w)) →
      w ≠ 0 → I.toNat + stride ≤ N.toNat)
    {F : Type} {s state post : PanSemStateFiniteExact 64 F} {D N watched : BitVec 64}
    (stage : ZeroStage s state D N watched) (small : D.toNat + N.toNat ≤ 33806089496)
    (separate : ∀ offset : Nat, offset < N.toNat →
      watched ≠ D + BitVec.ofNat 64 offset ∧ watched ≠ panByteAlignHOL (D + BitVec.ofNat 64 offset))
    (run : evaluateHOLFiniteState s (.while condition body) = (none,post)) : ZeroStage post state D N watched := by
  obtain ⟨sm,dL,nL,I,iL,iLe⟩ := stage
  obtain ⟨f1,f2,f3,_⟩ := zeroLoop_normal_separated_frame step condition guard s post D N watched I dL nL iL iLe small separate run
  exact ⟨f1.trans sm,(f2 _ (by decide)).trans dL,(f2 _ (by decide)).trans nL,f3⟩

theorem memzero_body_returned_separated_memory {F : Type} (state post : PanSemStateFiniteExact 64 F) (D N watched : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word D)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word N)))
    (small : D.toNat + N.toNat ≤ 33806089496)
    (separate : ∀ offset : Nat, offset < N.toNat →
      watched ≠ D + BitVec.ofNat 64 offset ∧ watched ≠ panByteAlignHOL (D + BitVec.ofNat 64 offset)) (v : ValueHOL 64)
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
                 have stage32 := ZeroStage.separated_loop memzeroWord32Body_zero _
                   (fun s I N w a b c d e f => memzero_block_guard 32 (by decide) s I N w a b c d e f)
                   stage0 small separate w32
                 exact ZeroStage.separated_loop memzeroWord8Body_zero _
                   (fun s I N w a b c d e f => memzero_block_guard 8 (by decide) s I N w a b c d e f)
                   stage32 small separate alignRun)
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
          have stageB := ZeroStage.separated_loop memzeroByte8Body_zero _
            (fun s I N w a b c d e f => memzero_block_guard 8 (by decide) s I N w a b c d e f)
            stageA small separate b8
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
              have stageC := ZeroStage.separated_loop memzeroByte1Body_zero _
                (fun s I N w a b c d e f => memzero_byte_guard s I N w a b c d e f)
                stageB small separate b1
              rw [evaluateHOLFiniteState_return] at r1
              simp only [eval_const_word] at r1
              repeat' (first | (split at r1) | skip)
              all_goals (try simp only [Prod.mk.injEq] at r1)
              all_goals (try obtain ⟨_,rfl⟩ := r1)
              all_goals first
                | (rw [m1]; exact stageC.1)
                | (simp at r1)

theorem memzero_call_normal_separated_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (D N watched : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word D),.val (.word N)])
    (code : state.code = originalRuntimeCode)
    (small : D.toNat + N.toNat ≤ 33806089496)
    (separate : ∀ offset : Nat, offset < N.toNat →
      watched ≠ D + BitVec.ofNat 64 offset ∧ watched ≠ panByteAlignHOL (D + BitVec.ofNat 64 offset))
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
  exact memzero_body_returned_separated_memory (callEntryStateHOLFinite state
      ((HolFiniteMapExact.empty.update (ofString "dst",.val (.word D))).update (ofString "n",.val (.word N))))
    output D N watched
    (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    small separate value bodyRun

#print axioms zeroLoop_normal_separated_frame
#print axioms ZeroStage.separated_loop
#print axioms memzero_body_returned_separated_memory
#print axioms memzero_call_normal_separated_memory
end InitECandidate.Runtime
