import InitECandidate.Runtime.CrepIfBudget
namespace InitECandidate.Runtime
open Flapjack
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

private theorem panGetByteWord8HOL_eq_getByteHOL8 {width : Nat}
    (a v : BitVec width) (be : Bool) :
    panGetByteWord8HOL a v be = getByteHOL8 a v be := by
  apply BitVec.eq_of_toNat_eq
  simp only [panGetByteWord8HOL, getByteHOL8, byteIndexHOL, BitVec.toNat_ofNat,
    BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  cases be <;> simp [Nat.pow_mul]

/-- Flapjack helper (no HOL declaration): HOL's ExtCall case proves
    `mem_load_byte_aux t.memory t.mdomain t.be = mem_load_byte s.memory
    s.memaddrs s.be` by extensionality under `mem_rel` and `state_rel`; this is
    that step over the exact carriers (for any decision procedure on the
    source domain). -/
private theorem panMemLoadByteWord8HOL_eq_memLoadByteAuxExact {width : Nat} [NeZero width]
    (smem : BitVec width → HolWordLab width) (dom : BitVec width → Prop) [DecidablePred dom]
    (tmem : BitVec width → WordLocW width) (tdom : BitVec width → Bool) (be : Bool)
    (hdom : dom = fun x => tdom x = true) (hm : crepToLoopMemRelHOLExact smem tmem dom) :
    panMemLoadByteWord8HOL smem dom be = memLoadByteAuxExact tmem tdom be := by
  funext a
  unfold panMemLoadByteWord8HOL memLoadByteAuxExact
  rw [riscvByteAlignHOL_eq_panByteAlignHOL]
  cases hv : smem (panByteAlignHOL a) with
  | word val =>
    simp only
    by_cases hd : dom (panByteAlignHOL a)
    · have hmv := hm _ hd
      rw [hv] at hmv
      have htd : tdom (panByteAlignHOL a) = true := by subst hdom; exact hd
      rw [if_pos hd, ← hmv]
      simp [wlabWlocExact, htd, panGetByteWord8HOL_eq_getByteHOL8, hv]
    · have htd : tdom (panByteAlignHOL a) = false := by
        subst hdom; simpa using hd
      rw [if_neg hd]
      cases htm : tmem (panByteAlignHOL a) <;> simp [htd]


private theorem write_bytearray_mem_rel_dom {width : Nat} [NeZero width]
    (nb : List (BitVec 8)) (sm : BitVec width → HolWordLab width)
    (tm : BitVec width → WordLocW width) (w : BitVec width)
    (dom : BitVec width → Prop) [inst : DecidablePred dom] (tdom : BitVec width → Bool)
    (be : Bool) (hdom : dom = fun a => tdom a = true)
    (h : crepToLoopMemRelHOLExact sm tm dom) :
    crepToLoopMemRelHOLExact (panWriteBytearrayWord8HOL w nb sm dom be)
      (writeBytearrayExact w nb tm tdom be) dom := by
  subst hdom
  have hi : inst = fun a => instDecidableEqBool (tdom a) true := Subsingleton.elim _ _
  subst hi
  exact write_bytearray_mem_rel nb sm tm w tdom be h

theorem crep_extCall_bounded {width : Nat} [NeZero width] {σ : Type} :
    ∀ (f : Flapjack.Basis.Pure.MlString.MlString) (c cl a al : Nat) (v1 : CrepSemHOLState width σ)
      (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
      (t : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (l : NumSet),
      evalCrepSemHOLProgExact v1 (.extCall f c cl a al) = (res, s1) ∧ res ≠ some .error ∧
        crepToLoopStateRelExact v1 t ∧
        crepToLoopMemRelHOLExact v1.memory t.memory v1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact v1.globals t.globals ∧
        crepToLoopCodeRelExact ctxt v1.code t.code ∧
        crepToLoopLocalsRelExact ctxt l v1.locals t.locals →
      ∃ (ck : Nat), ck ≤ 0 ∧ ∃ (res1 : Option (LoopSemStateFiniteExact.LoopResultExact width))
        (t1 : LoopSemStateFiniteExact width σ),
        LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l (.extCall f c cl a al))
            { t with clock := t.clock + ck } = (res1, t1) ∧
        crepToLoopStateRelExact s1 t1 ∧
        crepToLoopMemRelHOLExact s1.memory t1.memory s1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s1.globals t1.globals ∧
        crepToLoopCodeRelExact ctxt s1.code t1.code ∧
        res1 = resultToLoop res ∧
        localsResultRel ctxt l res s1 t1 := by
  intro f c cl a al v1 res s1 t ctxt l ⟨he, hne, hs, hm, hg, hc, hl⟩
  classical
  rw [evalCrepSemHOLProgExact_eq_evaluate_def] at he
  simp only at he
  -- all four source locals are words (otherwise the source errors)
  cases hcl : v1.locals.lookup cl with
  | none => simp [hcl] at he; exact absurd he.1.symm hne
  | some xcl =>
  cases hc' : v1.locals.lookup c with
  | none => simp [hcl, hc'] at he; exact absurd he.1.symm hne
  | some xc =>
  cases hal : v1.locals.lookup al with
  | none => simp [hcl, hc', hal] at he; exact absurd he.1.symm hne
  | some xal =>
  cases ha : v1.locals.lookup a with
  | none => simp [hcl, hc', hal, ha] at he; exact absurd he.1.symm hne
  | some xa =>
  cases xcl with | word wcl =>
  cases xc with | word wc =>
  cases xal with | word wal =>
  cases xa with | word wa =>
  simp only [hcl, hc', hal, ha] at he
  obtain ⟨ncl, hncl1, hncl2, hncl3⟩ := hl.2.2.2 cl _ hcl
  obtain ⟨nc, hnc1, hnc2, hnc3⟩ := hl.2.2.2 c _ hc'
  obtain ⟨nal, hnal1, hnal2, hnal3⟩ := hl.2.2.2 al _ hal
  obtain ⟨na, hna1, hna2, hna3⟩ := hl.2.2.2 a _ ha
  have hsub : LoopSemStateFiniteExact.sptSubsetLive l t.locals := hl.2.2.1
  rw [panMemLoadByteWord8HOL_eq_memLoadByteAuxExact v1.memory v1.memaddrs
    t.memory t.mdomain v1.be hs.1 hm] at he
  have hcomp : compileHOLExact ctxt l (.extCall f c cl a al) =
      (HolLoopProg.ffi f nc ncl na nal l : HolLoopProg width) := by
    simp [compileHOLExact, hnc1, hncl1, hna1, hnal1]
  rw [hcomp]
  obtain ⟨hdom, hsh, hclk, hbe, hffi, hba, hta⟩ := hs
  rw [hbe, hffi] at he
  have hcut : LoopSemStateFiniteExact.cutState l t = some { t with locals := sptInter t.locals l } :=
    LoopSemStateFiniteExact.cutState_of_subset l t hsub
  have ht0 : ({ t with clock := t.clock + 0 } : LoopSemStateFiniteExact width σ) = t := rfl
  have hlocals : crepToLoopLocalsRelExact ctxt l v1.locals (sptInter t.locals l) := by
    refine ⟨hl.1, hl.2.1, fun k hk => ?_, fun vn val hval => ?_⟩
    · have hk' : (sptLookup k l).isSome := hk
      show (sptLookup k (sptInter t.locals l)).isSome
      rw [sptLookup_sptInter, if_pos hk']
      exact hsub k hk
    · obtain ⟨n, hn1, hn2, hn3⟩ := hl.2.2.2 vn val hval
      have hnl : (sptLookup n l).isSome := hn2
      refine ⟨n, hn1, hn2, ?_⟩
      show sptLookup n (sptInter t.locals l) = _
      rw [sptLookup_sptInter, if_pos hnl]
      exact hn3
  cases hr1 : readBytearrayWordHOL wc wcl.toNat (memLoadByteAuxExact t.memory t.mdomain t.be) with
  | none => simp [hr1] at he; exact absurd he.1.symm hne
  | some cb =>
  cases hr2 : readBytearrayWordHOL wa wal.toNat (memLoadByteAuxExact t.memory t.mdomain t.be) with
  | none => simp [hr1, hr2] at he; exact absurd he.1.symm hne
  | some ab =>
  simp only [hr1, hr2] at he
  cases hf : callFFIHOL t.ffi (.extCall f) cb ab with
  | final ev =>
    simp only [hf, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    let tf : LoopSemStateFiniteExact width σ :=
      LoopSemStateFiniteExact.callEnv [] { t with locals := sptInter t.locals l }
    refine ⟨0, Nat.le_refl _, some (.finalFfi ev), tf, ?_, ⟨hdom, hsh, hclk, hbe, hffi, hba, hta⟩, hm, hg, hc,
      rfl, trivial⟩
    rw [ht0]
    simp only [LoopSemStateFiniteExact.evaluate, hncl3, hnc3, hnal3, hna3, wlabWlocHOL, hcut,
      hr1, hr2, hf, tf]
  | ret nf nb =>
    simp only [hf, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    let tf : LoopSemStateFiniteExact width σ :=
      { t with locals := sptInter t.locals l,
               memory := writeBytearrayExact wa nb t.memory t.mdomain t.be,
               ffi := nf }
    refine ⟨0, Nat.le_refl _, none, tf, ?_, ⟨hdom, hsh, hclk, rfl, rfl, hba, hta⟩, ?_, hg, hc, rfl, hlocals⟩
    · rw [ht0]
      simp only [LoopSemStateFiniteExact.evaluate, hncl3, hnc3, hnal3, hna3, wlabWlocHOL, hcut,
        hr1, hr2, hf, tf]
    · exact write_bytearray_mem_rel_dom nb v1.memory t.memory wa v1.memaddrs t.mdomain t.be
        hdom hm


#print axioms crep_extCall_bounded
end InitECandidate.Runtime
