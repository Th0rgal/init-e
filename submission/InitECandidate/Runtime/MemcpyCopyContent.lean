import InitECandidate.Runtime.HtabSetGrowFrame
import InitECandidate.Runtime.MemcpyAlignedSuffix
import InitECandidate.Runtime.MemcpyAlignedBody
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Guarded partial correctness of a normal loop exit, with the zero exit condition. -/
theorem while_normal_exit_guarded_cond (condition : ExpHOL 64) (body : ProgHOL 64)
    (Inv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (keeps : ∀ {F : Type} (s post : PanSemStateFiniteExact 64 F) (w : BitVec 64), Inv s →
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) condition = some (.val (.word w)) → w ≠ 0 →
      (evaluateHOLFiniteState (decClockHOLFinite s) body = (none,post) ∨
        evaluateHOLFiniteState (decClockHOLFinite s) body = (some .continue,post)) → Inv post)
    (noBreak : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState s body).1 ≠ some .break) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.clock = n → Inv state →
      ∀ post, evaluateHOLFiniteState state (.while condition body) = (none,post) →
        Inv post ∧ evalHOLFinite post (h := fun a => Classical.propDecidable (post.memaddrs a)) condition =
          some (.val (.word 0)) := by
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
      · rename_i zero
        simp only [Prod.mk.injEq] at run
        obtain ⟨_,rfl⟩ := run
        have : w = 0 := by simpa using zero
        subst this
        exact ⟨invariant,hw⟩
    · simp at run

#print axioms while_normal_exit_guarded_cond

/-- Word-copy progress: the copied prefix holds the source words and the memory
outside the destination is unchanged. -/
def CopyInv (D S N : BitVec 64) (M : BitVec 64 → HolWordLab 64) (A : BitVec 64 → Prop) {F : Type}
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ I : BitVec 64, s.locals.lookup (ofString "dst") = some (.val (.word D)) ∧
    s.locals.lookup (ofString "src") = some (.val (.word S)) ∧
    s.locals.lookup (ofString "n") = some (.val (.word N)) ∧
    s.locals.lookup (ofString "i") = some (.val (.word I)) ∧
    I.toNat % 8 = 0 ∧ I.toNat ≤ N.toNat ∧ s.memaddrs = A ∧ s.code = originalRuntimeCode ∧
    (∀ k : Nat, k < I.toNat → k % 8 = 0 → s.memory (D + BitVec.ofNat 64 k) = M (S + BitVec.ofNat 64 k)) ∧
    (∀ w : BitVec 64, (w.toNat < D.toNat ∨ D.toNat + N.toNat ≤ w.toNat) → s.memory w = M w)


/-- One word store of the copy extends the copied prefix by one word and keeps
the memory outside the destination. -/
theorem copy_word_store {F : Type} (s post : PanSemStateFiniteExact 64 F) (D S N I off : BitVec 64)
    (M : BitVec 64 → HolWordLab 64)
    (dL : s.locals.lookup (ofString "dst") = some (.val (.word D)))
    (sL : s.locals.lookup (ofString "src") = some (.val (.word S)))
    (iL : s.locals.lookup (ofString "i") = some (.val (.word I)))
    (small : D.toNat + N.toNat ≤ 33806089496) (smallS : S.toNat + N.toNat ≤ 33806089496)
    (disjoint : D.toNat + N.toNat ≤ S.toNat ∨ S.toNat + N.toNat ≤ D.toNat)
    (fits : I.toNat + off.toNat + 8 ≤ N.toNat) (offAligned : off.toNat % 8 = 0) (iAligned : I.toNat % 8 = 0)
    (srcMapped : s.memaddrs (S + I + off))
    (prefix' : ∀ k : Nat, k < I.toNat + off.toNat → k % 8 = 0 → s.memory (D + BitVec.ofNat 64 k) = M (S + BitVec.ofNat 64 k))
    (frame : ∀ w : BitVec 64, (w.toNat < D.toNat ∨ D.toNat + N.toNat ≤ w.toNat) → s.memory w = M w)
    (run : evaluateHOLFiniteState s (memcpyWordStore off) = (none,post)) :
    post.locals = s.locals ∧ post.memaddrs = s.memaddrs ∧ post.be = s.be ∧ post.code = s.code ∧
    (∀ k : Nat, k < I.toNat + off.toNat + 8 → k % 8 = 0 → post.memory (D + BitVec.ofNat 64 k) = M (S + BitVec.ofNat 64 k)) ∧
    (∀ w : BitVec 64, (w.toNat < D.toNat ∨ D.toNat + N.toNat ≤ w.toNat) → post.memory w = M w) := by
  have dNat : (D + I + off).toNat = D.toNat + I.toNat + off.toNat := by
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_add_of_lt (by omega)]; omega),BitVec.toNat_add_of_lt (by omega)]
  have sNat : (S + I + off).toNat = S.toNat + I.toNat + off.toNat := by
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_add_of_lt (by omega)]; omega),BitVec.toNat_add_of_lt (by omega)]
  obtain ⟨value,hv⟩ : ∃ value : BitVec 64, s.memory (S + I + off) = .word value := by
    cases h : s.memory (S + I + off) with | word x => exact ⟨x,rfl⟩
  have loaded : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (memcpyOffset (ofString "src") off)) = some (.val (.word value)) := by
    simp only [evalHOLExact,isWfShapeExactHOL]
    rw [eval_memcpyOffset s (ofString "src") S I off sL iL]
    simp [memLoadHOLExact,srcMapped,hv]
  have postEq := store_word_normal s post _ _ (D + I + off) value (eval_memcpyOffset s (ofString "dst") D I off dL iL) loaded run
  subst postEq
  have word : ∀ k : Nat, k < 2 ^ 64 → (BitVec.ofNat 64 k).toNat = k := fun k hk => by
    change k % 2 ^ 64 = k; exact Nat.mod_eq_of_lt hk
  refine ⟨rfl,rfl,rfl,rfl,?_,?_⟩
  · intro k inside aligned
    have dk : (D + BitVec.ofNat 64 k).toNat = D.toNat + k := by
      rw [BitVec.toNat_add_of_lt (by rw [word k (by omega)]; omega),word k (by omega)]
    have sk : (S + BitVec.ofNat 64 k).toNat = S.toNat + k := by
      rw [BitVec.toNat_add_of_lt (by rw [word k (by omega)]; omega),word k (by omega)]
    by_cases here : k = I.toNat + off.toNat
    · have e1 : D + BitVec.ofNat 64 k = D + I + off := BitVec.eq_of_toNat_eq (by rw [dk,dNat]; omega)
      have e2 : S + BitVec.ofNat 64 k = S + I + off := BitVec.eq_of_toNat_eq (by rw [sk,sNat]; omega)
      rw [e1,e2]
      simp only [sourceWriteWord,if_true]
      rw [← hv]
      exact frame _ (by rw [sNat]; omega)
    · have lt : k < I.toNat + off.toNat := by omega
      have ne : D + BitVec.ofNat 64 k ≠ D + I + off := word_ne_of_toNat (by rw [dk,dNat]; omega)
      simp only [sourceWriteWord,if_neg ne]
      exact prefix' k lt aligned
  · intro w outside
    have ne : w ≠ D + I + off := word_ne_of_toNat (by rw [dNat]; omega)
    simp only [sourceWriteWord,if_neg ne]
    exact frame w outside

#print axioms copy_word_store

theorem evaluate_memzeroAdvance {F : Type} (s : PanSemStateFiniteExact 64 F) (stride I : BitVec 64)
    (iL : s.locals.lookup (ofString "i") = some (.val (.word I))) :
    evaluateHOLFiniteState s (memzeroAdvance stride) = (none,setVarHOLFinite (ofString "i") (.val (.word (I + stride))) s) := by
  classical
  simp [memzeroAdvance,evaluateHOLFiniteState_assign,evalHOLExact,evalListHOLExact,iL,wordOpHOL,wordOp,valueIsWord,
    valueWord,isValidValueHOLExact,lookupKvarHOLExact,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite]

theorem copyInv_guard {F : Type} (s : PanSemStateFiniteExact 64 F) (I N stride w : BitVec 64)
    (iL : s.locals.lookup (ofString "i") = some (.val (.word I)))
    (nL : s.locals.lookup (ofString "n") = some (.val (.word N)))
    (inside : I.toNat ≤ N.toNat) (small : N.toNat ≤ 33806089496) (strideSmall : stride.toNat ≤ 32)
    (hw : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) (memzeroBlockCondition stride) =
      some (.val (.word w))) (nonzero : w ≠ 0) :
    I.toNat + stride.toNat ≤ N.toNat := by
  rw [evalHOLFinite_eq_toExact,eval_memzero_block_condition s I N stride iL nL] at hw
  simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at hw
  have added : (I + stride).toNat = I.toNat + stride.toNat := by
    rw [BitVec.toNat_add_of_lt (by omega)]
  by_cases h : Compiler.Encoders.Asm.wordCmpHOL .notLower N (I + stride) = true
  · change (!decide (N.toNat < (I + stride).toNat)) = true at h
    simp only [Bool.not_eq_true',decide_eq_false_iff_not] at h
    omega
  · rw [if_neg h] at hw; exact absurd hw.symm nonzero

/-- A word32 copy iteration under its guard keeps the copy invariant. -/
theorem copyInv_word32 {F : Type} (s post : PanSemStateFiniteExact 64 F) (D S N : BitVec 64) (M : BitVec 64 → HolWordLab 64)
    (A : BitVec 64 → Prop) (w : BitVec 64)
    (small : D.toNat + N.toNat ≤ 33806089496) (smallS : S.toNat + N.toNat ≤ 33806089496)
    (disjoint : D.toNat + N.toNat ≤ S.toNat ∨ S.toNat + N.toNat ≤ D.toNat)
    (srcDomain : ∀ k : Nat, k < N.toNat → k % 8 = 0 → A (S + BitVec.ofNat 64 k))
    (inv : CopyInv D S N M A s)
    (hw : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) (memzeroBlockCondition 32) =
      some (.val (.word w))) (nonzero : w ≠ 0)
    (run : evaluateHOLFiniteState (decClockHOLFinite s) memcpyWord32Body = (none,post)) :
    CopyInv D S N M A post := by
  obtain ⟨I,dL,sL,nL,iL,iA,iLe,sA,sC,pre,frame⟩ := inv
  have fits := copyInv_guard s I N 32 w iL nL iLe (by omega) (by decide) hw nonzero
  change I.toNat + 32 ≤ N.toNat at fits
  have mapped : ∀ off : BitVec 64, off.toNat % 8 = 0 → I.toNat + off.toNat + 8 ≤ N.toNat → A (S + I + off) := by
    intro off oa ofits
    have e : S + I + off = S + BitVec.ofNat 64 (I.toNat + off.toNat) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_add_of_lt (by omega)]; omega),BitVec.toNat_add_of_lt (by omega),
        BitVec.toNat_add_of_lt (by rw [show (BitVec.ofNat 64 (I.toNat + off.toNat)).toNat = I.toNat + off.toNat from
          Nat.mod_eq_of_lt (by omega)]; omega),
        show (BitVec.ofNat 64 (I.toNat + off.toNat)).toNat = I.toNat + off.toNat from Nat.mod_eq_of_lt (by omega)]
      omega
    rw [e]; exact srcDomain _ (by omega) (by omega)
  unfold memcpyWord32Body at run
  obtain ⟨s1,r1,run⟩ := seq_normal_parts run
  obtain ⟨l1,a1,b1,c1,p1,f1⟩ := copy_word_store (decClockHOLFinite s) s1 D S N I 0 M dL sL iL small smallS disjoint
    (by change _ + 0 + 8 ≤ _; omega) (by decide) iA
    (by rw [show (decClockHOLFinite s).memaddrs = A from sA]; exact mapped 0 (by decide) (by change _ + 0 + 8 ≤ _; omega))
    (by intro k hk ha; exact pre k (by change k < _ + 0 at hk; omega) ha) frame r1
  obtain ⟨s2,r2,run⟩ := seq_normal_parts run
  obtain ⟨l2,a2,b2,c2,p2,f2⟩ := copy_word_store s1 s2 D S N I 8 M (by rw [l1]; exact dL) (by rw [l1]; exact sL)
    (by rw [l1]; exact iL) small smallS disjoint (by change _ + 8 + 8 ≤ _; omega) (by decide) iA
    (by rw [a1,show (decClockHOLFinite s).memaddrs = A from sA]; exact mapped 8 (by decide) (by change _ + 8 + 8 ≤ _; omega))
    (by intro k hk ha; exact p1 k (by change k < _ + 0 + 8; change k < _ + 8 at hk; omega) ha) f1 r2
  obtain ⟨s3,r3,run⟩ := seq_normal_parts run
  obtain ⟨l3,a3,b3,c3,p3,f3⟩ := copy_word_store s2 s3 D S N I 16 M (by rw [l2,l1]; exact dL) (by rw [l2,l1]; exact sL)
    (by rw [l2,l1]; exact iL) small smallS disjoint (by change _ + 16 + 8 ≤ _; omega) (by decide) iA
    (by rw [a2,a1,show (decClockHOLFinite s).memaddrs = A from sA]; exact mapped 16 (by decide) (by change _ + 16 + 8 ≤ _; omega))
    (by intro k hk ha; exact p2 k (by change k < _ + 8 + 8; change k < _ + 16 at hk; omega) ha) f2 r3
  obtain ⟨s4,r4,run⟩ := seq_normal_parts run
  obtain ⟨l4,a4,b4,c4,p4,f4⟩ := copy_word_store s3 s4 D S N I 24 M (by rw [l3,l2,l1]; exact dL) (by rw [l3,l2,l1]; exact sL)
    (by rw [l3,l2,l1]; exact iL) small smallS disjoint (by change _ + 24 + 8 ≤ _; omega) (by decide) iA
    (by rw [a3,a2,a1,show (decClockHOLFinite s).memaddrs = A from sA]; exact mapped 24 (by decide) (by change _ + 24 + 8 ≤ _; omega))
    (by intro k hk ha; exact p3 k (by change k < _ + 16 + 8; change k < _ + 24 at hk; omega) ha) f3 r4
  rw [evaluate_memzeroAdvance s4 32 I (by rw [l4,l3,l2,l1]; exact iL)] at run
  cases run
  have i32 : (I + 32).toNat = I.toNat + 32 := by rw [BitVec.toNat_add_of_lt (by change _ + 32 < _; omega)]; rfl
  have keep : ∀ k, k ≠ ofString "i" → (setVarHOLFinite (ofString "i") (.val (.word (I + 32))) s4).locals.lookup k =
      s.locals.lookup k := by
    intro k ne; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne]; rw [l4,l3,l2,l1]; rfl
  refine ⟨I + 32,(keep _ (by decide)).trans dL,(keep _ (by decide)).trans sL,(keep _ (by decide)).trans nL,
    by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],by rw [i32]; omega,by rw [i32]; omega,
    by change s4.memaddrs = A; rw [a4,a3,a2,a1]; exact sA,by change s4.code = _; rw [c4,c3,c2,c1]; exact sC,
    fun k hk ha => p4 k (by rw [i32] at hk; change k < _ + 24 + 8; omega) ha,f4⟩

#print axioms copyInv_word32

/-- A word8 copy iteration under its guard keeps the copy invariant. -/
theorem copyInv_word8 {F : Type} (s post : PanSemStateFiniteExact 64 F) (D S N : BitVec 64) (M : BitVec 64 → HolWordLab 64)
    (A : BitVec 64 → Prop) (w : BitVec 64)
    (small : D.toNat + N.toNat ≤ 33806089496) (smallS : S.toNat + N.toNat ≤ 33806089496)
    (disjoint : D.toNat + N.toNat ≤ S.toNat ∨ S.toNat + N.toNat ≤ D.toNat)
    (srcDomain : ∀ k : Nat, k < N.toNat → k % 8 = 0 → A (S + BitVec.ofNat 64 k))
    (inv : CopyInv D S N M A s)
    (hw : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) (memzeroBlockCondition 8) =
      some (.val (.word w))) (nonzero : w ≠ 0)
    (run : evaluateHOLFiniteState (decClockHOLFinite s) memcpyWord8Body = (none,post)) :
    CopyInv D S N M A post := by
  obtain ⟨I,dL,sL,nL,iL,iA,iLe,sA,sC,pre,frame⟩ := inv
  have fits := copyInv_guard s I N 8 w iL nL iLe (by omega) (by decide) hw nonzero
  change I.toNat + 8 ≤ N.toNat at fits
  have mapped : A (S + I + 0) := by
    have e : S + I + 0 = S + BitVec.ofNat 64 I.toNat := by simp
    rw [e]; exact srcDomain _ (by omega) iA
  have shape : memcpyWord8Body = .seq (memcpyWordStore 0) (memzeroAdvance 8) := rfl
  rw [shape] at run
  obtain ⟨s1,r1,run⟩ := seq_normal_parts run
  obtain ⟨l1,a1,b1,c1,p1,f1⟩ := copy_word_store (decClockHOLFinite s) s1 D S N I 0 M dL sL iL small smallS disjoint
    (by change _ + 0 + 8 ≤ _; omega) (by decide) iA
    (by rw [show (decClockHOLFinite s).memaddrs = A from sA]; exact mapped)
    (by intro k hk ha; exact pre k (by change k < _ + 0 at hk; omega) ha) frame r1
  rw [evaluate_memzeroAdvance s1 8 I (by rw [l1]; exact iL)] at run
  cases run
  have i8 : (I + 8).toNat = I.toNat + 8 := by rw [BitVec.toNat_add_of_lt (by change _ + 8 < _; omega)]; rfl
  have keep : ∀ k, k ≠ ofString "i" → (setVarHOLFinite (ofString "i") (.val (.word (I + 8))) s1).locals.lookup k =
      s.locals.lookup k := by
    intro k ne; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne]; rw [l1]; rfl
  refine ⟨I + 8,(keep _ (by decide)).trans dL,(keep _ (by decide)).trans sL,(keep _ (by decide)).trans nL,
    by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],by rw [i8]; omega,by rw [i8]; omega,
    by change s1.memaddrs = A; rw [a1]; exact sA,by change s1.code = _; rw [c1]; exact sC,
    fun k hk ha => p1 k (by rw [i8] at hk; change k < _ + 0 + 8; omega) ha,f1⟩

theorem copyInv_word32_loop {F : Type} (s post : PanSemStateFiniteExact 64 F) (D S N : BitVec 64) (M : BitVec 64 → HolWordLab 64)
    (A : BitVec 64 → Prop)
    (small : D.toNat + N.toNat ≤ 33806089496) (smallS : S.toNat + N.toNat ≤ 33806089496)
    (disjoint : D.toNat + N.toNat ≤ S.toNat ∨ S.toNat + N.toNat ≤ D.toNat)
    (srcDomain : ∀ k : Nat, k < N.toNat → k % 8 = 0 → A (S + BitVec.ofNat 64 k))
    (inv : CopyInv D S N M A s)
    (run : evaluateHOLFiniteState s memcpyWord32Loop = (none,post)) : CopyInv D S N M A post := by
  rw [source_memcpy_word32_loop] at run
  exact (while_normal_exit_guarded_cond _ memcpyWord32Body (fun s => CopyInv D S N M A s)
    (fun s post w i hw nz flow => by
      rcases flow with normal | cont
      · exact copyInv_word32 s post D S N M A w small smallS disjoint srcDomain i hw nz normal
      · exact absurd (congrArg Prod.fst cont) (evaluate_noTopContinue memcpyWord32Body (by decide) _))
    (fun s => evaluate_noTopBreak memcpyWord32Body (by decide) s) s.clock s rfl inv post run).1

theorem copyInv_word8_loop {F : Type} (s post : PanSemStateFiniteExact 64 F) (D S N : BitVec 64) (M : BitVec 64 → HolWordLab 64)
    (A : BitVec 64 → Prop)
    (small : D.toNat + N.toNat ≤ 33806089496) (smallS : S.toNat + N.toNat ≤ 33806089496)
    (disjoint : D.toNat + N.toNat ≤ S.toNat ∨ S.toNat + N.toNat ≤ D.toNat)
    (srcDomain : ∀ k : Nat, k < N.toNat → k % 8 = 0 → A (S + BitVec.ofNat 64 k)) (n8 : N.toNat % 8 = 0)
    (inv : CopyInv D S N M A s)
    (run : evaluateHOLFiniteState s (.while (memzeroBlockCondition 8) memcpyWord8Body) = (none,post)) :
    CopyInv D S N M A post ∧ post.locals.lookup (ofString "i") = some (.val (.word N)) := by
  obtain ⟨inv',exit⟩ := while_normal_exit_guarded_cond _ memcpyWord8Body (fun s => CopyInv D S N M A s)
    (fun s post w i hw nz flow => by
      rcases flow with normal | cont
      · exact copyInv_word8 s post D S N M A w small smallS disjoint srcDomain i hw nz normal
      · exact absurd (congrArg Prod.fst cont) (evaluate_noTopContinue memcpyWord8Body (by decide) _))
    (fun s => evaluate_noTopBreak memcpyWord8Body (by decide) s) s.clock s rfl inv post run
  refine ⟨inv',?_⟩
  obtain ⟨I,_,_,nL,iL,iA,iLe,_⟩ := inv'
  rw [evalHOLFinite_eq_toExact,eval_memzero_block_condition post I N 8 iL nL] at exit
  simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at exit
  have added : (I + 8).toNat = I.toNat + 8 := by rw [BitVec.toNat_add_of_lt (by change _ + 8 < _; omega)]; rfl
  have eq : I = N := by
    apply BitVec.eq_of_toNat_eq
    by_cases h : Compiler.Encoders.Asm.wordCmpHOL .notLower N (I + 8) = true
    · rw [if_pos h] at exit; exact absurd exit (by decide)
    · change ¬ ((!decide (N.toNat < (I + 8).toNat)) = true) at h
      simp only [Bool.not_eq_true',decide_eq_false_iff_not,not_not] at h
      omega
  rw [← eq]; exact iL

#print axioms copyInv_word8_loop

theorem while_noTopReturn {F : Type} (condition : ExpHOL 64) (body : ProgHOL 64) (supported : noTopReturn body = true)
    (s post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (run : evaluateHOLFiniteState s (.while condition body) = (some (.returned v),post)) : False :=
  while_returned_invariant _ body (fun _ => True) (fun _ => False) (fun _ _ => trivial)
    (fun t w q _ r => evaluate_noTopReturn body supported t w (by rw [r])) (fun _ _ _ _ => trivial)
    s.clock s rfl trivial v post run

theorem evaluate_memcpy_byte1_done {F : Type} (s : PanSemStateFiniteExact 64 F) (N : BitVec 64)
    (iL : s.locals.lookup (ofString "i") = some (.val (.word N)))
    (nL : s.locals.lookup (ofString "n") = some (.val (.word N))) :
    evaluateHOLFiniteState s memcpyByte1Loop = (none,s) := by
  rw [source_memcpy_byte1_loop,evaluateHOLFiniteState_while_total]
  simp [evalHOLFinite_eq_toExact,evalHOLExact,iL,nL,Compiler.Encoders.Asm.wordCmpHOL]

/-- A returned original memcpy body on aligned, disjoint, word-multiple regions
copies every source word to the destination and changes nothing else. -/
theorem memcpy_body_returned_copy {F : Type} (state post : PanSemStateFiniteExact 64 F) (D S N : BitVec 64) (v : ValueHOL 64)
    (dL : state.locals.lookup (ofString "dst") = some (.val (.word D)))
    (sL : state.locals.lookup (ofString "src") = some (.val (.word S)))
    (nL : state.locals.lookup (ofString "n") = some (.val (.word N)))
    (code : state.code = originalRuntimeCode) (dA : D.toNat % 8 = 0) (sA : S.toNat % 8 = 0) (n8 : N.toNat % 8 = 0)
    (small : D.toNat + N.toNat ≤ 33806089496) (smallS : S.toNat + N.toNat ≤ 33806089496)
    (disjoint : D.toNat + N.toNat ≤ S.toNat ∨ S.toNat + N.toNat ≤ D.toNat)
    (srcDomain : ∀ k : Nat, k < N.toNat → k % 8 = 0 → state.memaddrs (S + BitVec.ofNat 64 k))
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_memcpy) = (some (.returned v),post)) :
    (∀ k : Nat, k < N.toNat → k % 8 = 0 → post.memory (D + BitVec.ofNat 64 k) = state.memory (S + BitVec.ofNat 64 k)) ∧
    (∀ w : BitVec 64, (w.toNat < D.toNat ∨ D.toNat + N.toNat ≤ w.toNat) → post.memory w = state.memory w) ∧
    post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  rw [source_memcpy_scoped_body] at run
  obtain ⟨iv,inner,ie,run0,m0,a0,b0,c0⟩ := dec_returned_state run
  rw [eval_const_word] at ie
  cases ie
  generalize hs0 : setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state = s0 at run0
  have l0 : ∀ k, k ≠ ofString "i" → s0.locals.lookup k = state.locals.lookup k := by
    intro k ne; rw [← hs0]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne]
  have dL0 := (l0 _ (by decide)).trans dL
  have sL0 := (l0 _ (by decide)).trans sL
  have nL0 := (l0 _ (by decide)).trans nL
  have iL0 : s0.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    rw [← hs0]; simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have choice : evaluateHOLFiniteState s0
      (.ite memcpyAlignmentCondition (.seq memcpyWord32Loop memcpyWord8Loop) .skip) =
        evaluateHOLFiniteState s0 (.seq memcpyWord32Loop memcpyWord8Loop) := by
    rw [evaluateHOLFiniteState_ite,eval_memcpy_aligned_condition s0 D S dL0 sL0 dA sA]
    rfl
  unfold memcpyAfterIndex at run0
  rw [evaluateHOLFiniteState_seq_line780,choice] at run0
  have inv0 : CopyInv D S N state.memory state.memaddrs s0 :=
    ⟨0,dL0,sL0,nL0,iL0,by decide,by simp,by rw [← hs0]; rfl,by rw [← hs0]; exact code,fun k hk _ => by simp at hk,
      fun w _ => by rw [← hs0]; rfl⟩
  cases wordsRun : evaluateHOLFiniteState s0 (.seq memcpyWord32Loop memcpyWord8Loop) with
  | mk r mid =>
    rw [wordsRun] at run0
    cases r with
    | some res =>
      exfalso
      obtain ⟨e,_⟩ := Prod.mk.inj run0
      simp only [Option.some.injEq] at e
      subst e
      rw [evaluateHOLFiniteState_seq_line780] at wordsRun
      cases w32 : evaluateHOLFiniteState s0 memcpyWord32Loop with
      | mk r1 m1 =>
        rw [w32] at wordsRun
        cases r1 with
        | none =>
          simp only at wordsRun
          exact while_noTopReturn _ memcpyWord8Body (by decide) m1 mid v (by unfold memcpyWord8Loop at wordsRun; exact wordsRun)
        | some r1 =>
          obtain ⟨e1,_⟩ := Prod.mk.inj wordsRun
          simp only [Option.some.injEq] at e1
          subst e1
          rw [source_memcpy_word32_loop] at w32
          exact while_noTopReturn _ memcpyWord32Body (by decide) s0 m1 v w32
    | none =>
      simp only at run0
      obtain ⟨m1,w32,w8⟩ := seq_normal_parts wordsRun
      have inv1 := copyInv_word32_loop s0 m1 D S N state.memory state.memaddrs small smallS disjoint srcDomain inv0 w32
      obtain ⟨inv2,iN⟩ := copyInv_word8_loop m1 mid D S N state.memory state.memaddrs small smallS disjoint srcDomain n8 inv1
        (by unfold memcpyWord8Loop at w8; exact w8)
      obtain ⟨I,_,_,nLm,iLm,_,_,mA,_,pre,frame⟩ := inv2
      have IN : I = N := by
        rw [iN] at iLm
        simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at iLm
        exact iLm.symm
      rw [evaluateHOLFiniteState_seq_line780,evaluate_memcpy_byte8_skip mid N N iN nLm (le_refl _) (by omega) (by omega)] at run0
      simp only at run0
      rw [evaluateHOLFiniteState_seq_line780,evaluate_memcpy_byte1_done mid N iN nLm] at run0
      simp only at run0
      obtain ⟨rm,ra,rb,_⟩ := return_const_state mid inner 0 v run0
      have midMeta := evaluateHOLFiniteState_metadata s0 (.seq memcpyWord32Loop memcpyWord8Loop)
      rw [wordsRun] at midMeta
      subst IN
      refine ⟨fun k hk ha => by rw [m0,rm]; exact pre k hk ha,fun w h => by rw [m0,rm]; exact frame w h,
        by rw [a0,ra]; exact mA,by rw [b0,rb,midMeta.2.2.1,← hs0]; rfl⟩

#print axioms memcpy_body_returned_copy

/-- A normally finishing discarded memcpy call on aligned, disjoint, word-multiple
regions copies every source word and changes nothing else. -/
theorem memcpy_call_normal_copy {F : Type} (state post : PanSemStateFiniteExact 64 F) (arguments : List (ExpHOL 64))
    (D S N : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word D),.val (.word S),.val (.word N)])
    (code : state.code = originalRuntimeCode) (dA : D.toNat % 8 = 0) (sA : S.toNat % 8 = 0) (n8 : N.toNat % 8 = 0)
    (small : D.toNat + N.toNat ≤ 33806089496) (smallS : S.toNat + N.toNat ≤ 33806089496)
    (disjoint : D.toNat + N.toNat ≤ S.toNat ∨ S.toNat + N.toNat ≤ D.toNat)
    (srcDomain : ∀ k : Nat, k < N.toNat → k % 8 = 0 → state.memaddrs (S + BitVec.ofNat 64 k))
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "memcpy") arguments) = (none,post)) :
    (∀ k : Nat, k < N.toNat → k % 8 = 0 → post.memory (D + BitVec.ofNat 64 k) = state.memory (S + BitVec.ofNat 64 k)) ∧
    (∀ w : BitVec 64, (w.toNat < D.toNat ∨ D.toNat + N.toNat ≤ w.toNat) → post.memory w = state.memory w) ∧
    post.locals = state.locals ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ post.code = state.code := by
  have installed : state.code.lookup (ofString "memcpy") =
      some ([(ofString "dst",.one),(ofString "src",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_memcpy,.one) := by
    rw [code]; exact originalRuntimeCode_memcpy_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "memcpy") (ofString "dst") (ofString "src") (ofString "n")
    (sourceFunctionBody Guest.guestFn_memcpy) D S N (by decide) (by decide) (by decide) installed
  obtain ⟨v,output,bodyRun,memory,locals⟩ := evaluate_discard_normal_body_memory state post (ofString "memcpy")
    _ _ _ _ .one args lookup run
  obtain ⟨content,frame,_,_⟩ := memcpy_body_returned_copy _ output D S N v
    (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) (by exact code) dA sA n8 small smallS disjoint
    (fun k hk ha => by exact srcDomain k hk ha) bodyRun
  have meta' := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "memcpy") arguments)
  rw [run] at meta'
  exact ⟨fun k hk ha => by rw [memory]; exact content k hk ha,fun w h => by rw [memory]; exact frame w h,locals,meta'.2.1,
    meta'.2.2.1,meta'.1⟩

#print axioms memcpy_call_normal_copy
end InitECandidate.Runtime
