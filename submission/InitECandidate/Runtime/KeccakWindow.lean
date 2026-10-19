import InitECandidate.Runtime.StoreLoopWindow
import InitECandidate.Runtime.KeccakFBodyBound
import InitECandidate.Runtime.KeccakGlobalsFrame
import InitECandidate.Runtime.PanSingleWordLookup
import InitECandidate.Runtime.PanTwoWordLookup
import InitECandidate.Runtime.PanThreeWordLookup
import InitECandidate.Runtime.PanDiscardNormalBodyMemory
import InitECandidate.Runtime.OriginalKeccakCode
import InitECandidate.Runtime.OriginalMemzeroCode
import InitECandidate.Runtime.OriginalMemcpyCode
import InitECandidate.Runtime.OriginalKeccakAbsorbCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Writing a byte array at `address` keeps every word that is not the aligned word of one of its bytes. -/
theorem writeBytes_frame (bytes : List (BitVec 8)) : ∀ (address : BitVec 64) (memory : BitVec 64 → HolWordLab 64)
    (domain : BitVec 64 → Prop) [DecidablePred domain] (be : Bool) (w : BitVec 64),
    (∀ j : Nat, j < bytes.length → w ≠ panByteAlignHOL (address + BitVec.ofNat 64 j)) →
    panWriteBytearrayWord8HOL address bytes memory domain be w = memory w := by
  induction bytes with
  | nil => intro _ _ _ _ _ _ _; rfl
  | cons byte rest ih =>
    intro address memory domain _ be w out
    have e1 : (1 : BitVec 64).toNat = 1 := rfl
    have restKeep := ih (address + 1) memory domain be w (fun j hj => by
      have := out (j + 1) (by simp; omega)
      rwa [show address + 1 + BitVec.ofNat 64 j = address + BitVec.ofNat 64 (j + 1) by
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add,BitVec.toNat_ofNat,e1]; omega])
    have ne : w ≠ panByteAlignHOL address := by
      have := out 0 (by simp); simpa using this
    simp only [panWriteBytearrayWord8HOL]
    rcases hs : panMemStoreByteWord8HOL (panWriteBytearrayWord8HOL (address + 1) rest memory domain be) domain be
      address byte with _ | updated
    · rfl
    · simp only [panMemStoreByteWord8HOL] at hs
      split at hs
      · simp only [Option.some.injEq] at hs
        rw [← hs]
        simp only [if_neg ne]
        exact restKeep
      · cases hs

#print axioms writeBytes_frame

theorem callFFIHOL_ret_length {σ : Type} (st : HolFfiState σ) (name : HolFfiName) (conf bytes : List (BitVec 8))
    (st' : HolFfiState σ) (nb : List (BitVec 8)) (h : callFFIHOL st name conf bytes = .ret st' nb) :
    nb.length = bytes.length := by
  unfold callFFIHOL at h
  split at h
  · cases h; rfl
  · split at h
    · split at h
      · cases h; assumption
      · cases h
    · cases h

set_option maxHeartbeats 2000000 in
theorem keccakf_extCall_window {F : Type} (s : PanSemStateFiniteExact 64 F) (S w : BitVec 64)
    (hS : s.locals.lookup (ofString "stp") = some (.val (.word S)))
    (out : ∀ j : Nat, j < 200 → w ≠ panByteAlignHOL (S + BitVec.ofNat 64 j)) :
    (evaluateHOLFiniteState s (.extCall (ofString "keccakf") (.var .local (ofString "stp")) (.const 0)
      (.var .local (ofString "stp")) (.const 200))).2.memory w = s.memory w := by
  have eS : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) (.var .local (ofString "stp")) =
      some (.val (.word S)) := by rw [evalHOLFinite_eq_toExact]; simp [evalHOLExact,hS]
  have e0 : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) (.const 0) =
      some (.val (.word 0)) := by rw [evalHOLFinite_eq_toExact]; rfl
  have e200 : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) (.const 200) =
      some (.val (.word 200)) := by rw [evalHOLFinite_eq_toExact]; rfl
  rw [evaluateHOLFiniteState_extCall_source]
  simp only [eS,e0,e200]
  split
  · rename_i bytes1 bytes2 _ r2
    have len := readBytearrayWordHOL_length _ _ _ bytes2 r2
    split
    · rfl
    · rename_i newFfi newBytes hret
      have nl := callFFIHOL_ret_length _ _ _ _ _ _ hret
      exact @writeBytes_frame newBytes S s.memory s.memaddrs (fun a => Classical.propDecidable (s.memaddrs a)) s.be w
        (fun j hj => out j (by
        have : (200 : BitVec 64).toNat = 200 := rfl; omega))
  · rfl

/-- The original `keccak_f1600(stp)` writes only the aligned words of `[S, S + 200)`, in every outcome (the
foreign `@keccakf` call returns exactly as many bytes as it is given, or ends the run). -/
theorem keccakF_body_window {F : Type} (s : PanSemStateFiniteExact 64 F) (S w : BitVec 64)
    (hS : s.locals.lookup (ofString "stp") = some (.val (.word S)))
    (out : ∀ j : Nat, j < 200 → w ≠ panByteAlignHOL (S + BitVec.ofNat 64 j)) :
    (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_keccak_f1600)).2.memory w = s.memory w := by
  have ex := keccakf_extCall_window s S w hS out
  rw [source_keccakF1600_body,evaluateHOLFiniteState_seq_line780]
  cases r : evaluateHOLFiniteState s (.extCall (ofString "keccakf") (.var .local (ofString "stp")) (.const 0)
      (.var .local (ofString "stp")) (.const 200)) with
  | mk res m =>
    rw [r] at ex
    cases res with
    | some x => exact ex
    | none =>
      dsimp only
      rw [congrFun (evaluate_readOnly_memory (.return (.const 0)) (by decide) m) w]
      exact ex

#print axioms keccakF_body_window

theorem isWord_op {F : Type} (s : PanSemStateFiniteExact 64 F) (o : BinOp) (es : List (ExpHOL 64)) (x : ValueHOL 64)
    (hx : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.op o es) = some x) :
    ∃ y : BitVec 64, x = .val (.word y) := by
  simp only [evalHOLExact] at hx
  split at hx
  · split at hx
    · obtain ⟨y,-,hy⟩ := Option.map_eq_some_iff.mp hx
      exact ⟨y,hy.symm⟩
    · cases hx
  · cases hx

theorem cond_lessConst {F : Type} (s : PanSemStateFiniteExact 64 F) (I v : BitVec 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word I)))
    (hv : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .less (.var .local (ofString "i")) (.const 136)) = some (.val (.word v))) (nz : v ≠ 0)
    (small : I.toNat < 144) : I.toNat < 136 := by
  rw [evalHOLFinite_eq_toExact] at hv
  simp [evalHOLExact,hi,Compiler.Encoders.Asm.wordCmpHOL] at hv
  by_cases c : Compiler.Encoders.Asm.holAsmSignedLess I 136#64 = true
  · unfold Compiler.Encoders.Asm.holAsmSignedLess at c
    have e136 : (136#64).toNat = 136 := rfl
    simp only [e136] at c
    split at c
    · split at c
      · simpa using c
      · cases c
    · omega
  · simp [c] at hv; exact absurd hv.symm nz

def absorbP (S Bk : BitVec 64) (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  L.lookup (ofString "stp") = some (.val (.word S)) ∧ L.lookup (ofString "blk") = some (.val (.word Bk))

theorem absorbP_stable (S Bk : BitVec 64) : ∀ L L' : HolFiniteMapExact MlS (ValueHOL 64), absorbP S Bk L →
    (∀ name, name ≠ ofString "i" → L'.lookup name = L.lookup name) → absorbP S Bk L' :=
  fun _ _ p f => ⟨(f _ (by decide)).trans p.1,(f _ (by decide)).trans p.2⟩

def absorbAStep : ProgHOL 64 := (.seq (.store (.op .add [(.var .local (ofString "stp")),(.var .local (ofString "i"))]) (.op .xor [(.load .one (.op .add [(.var .local (ofString "stp")),(.var .local (ofString "i"))])),(.load .one (.op .add [(.var .local (ofString "blk")),(.var .local (ofString "i"))]))])) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 8)])))

def absorbBStep : ProgHOL 64 := (.seq (.store (.op .add [(.var .local (ofString "stp")),(.var .local (ofString "i"))]) (.op .xor [(.load .one (.op .add [(.var .local (ofString "stp")),(.var .local (ofString "i"))])),(.op .or [(.loadByte (.op .add [(.var .local (ofString "blk")),(.var .local (ofString "i"))])),(.shift .lsl (.loadByte (.op .add [(.var .local (ofString "blk")),(.var .local (ofString "i")),(.const 1)])) (.const 8)),(.shift .lsl (.loadByte (.op .add [(.var .local (ofString "blk")),(.var .local (ofString "i")),(.const 2)])) (.const 16)),(.shift .lsl (.loadByte (.op .add [(.var .local (ofString "blk")),(.var .local (ofString "i")),(.const 3)])) (.const 24)),(.shift .lsl (.op .or [(.loadByte (.op .add [(.var .local (ofString "blk")),(.var .local (ofString "i")),(.const 4)])),(.shift .lsl (.loadByte (.op .add [(.var .local (ofString "blk")),(.var .local (ofString "i")),(.const 4),(.const 1)])) (.const 8)),(.shift .lsl (.loadByte (.op .add [(.var .local (ofString "blk")),(.var .local (ofString "i")),(.const 4),(.const 2)])) (.const 16)),(.shift .lsl (.loadByte (.op .add [(.var .local (ofString "blk")),(.var .local (ofString "i")),(.const 4),(.const 3)])) (.const 24))]) (.const 32))])])) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 8)])))


/-- An absorb loop (`while i < 136 { st stp + i, ...; i = i + 8 }`) writes only inside `[S, S + 200)`. -/
theorem absorbLoop_window {F : Type} (step : ProgHOL 64) (S Bk w : BitVec 64)
    (adv : AdvStep (ofString "i") 8 step)
    (win : ∀ I : BitVec 64, (∀ c : BitVec 64, c.toNat < 1 → w ≠ S + I + c ∧ w ≠ panByteAlignHOL (S + I + c)) →
      WStep (fun L => absorbP S Bk L ∧ L.lookup (ofString "i") = some (.val (.word I))) w step)
    (out : ¬ MWin S 200 w) (s : PanSemStateFiniteExact 64 F)
    (inv : LoopInv (absorbP S Bk) (ofString "i") (fun I => I.toNat < 144) s) :
    (evaluateHOLFiniteState s (.while (.cmp .less (.var .local (ofString "i")) (.const 136)) step)).2.memory w =
      s.memory w ∧
      ((evaluateHOLFiniteState s (.while (.cmp .less (.var .local (ofString "i")) (.const 136)) step)).1 = none →
        LoopInv (absorbP S Bk) (ofString "i") (fun I => I.toNat < 144)
          (evaluateHOLFiniteState s (.while (.cmp .less (.var .local (ofString "i")) (.const 136)) step)).2) := by
  refine storeLoop_watch _ step _ 8 w (absorbP S Bk) _ adv (absorbP_stable S Bk) ?_ s inv
  intro s' I v p hi q hv nz
  have g := cond_lessConst s' I v hi hv nz q
  refine ⟨?_,win I (fun c hc => mwin_off out (by omega))⟩
  show (I + 8).toNat < 144
  rw [BitVec.toNat_add]; have : (8 : BitVec 64).toNat = 8 := rfl; rw [this]; omega

def absorbHOL : ProgHOL 64 := (.dec (ofString "i") .one (.const 0) (.seq (.ite (.cmp .equal (.op .and [(.var .local (ofString "blk")),(.const 7)]) (.const 0)) (.while (.cmp .less (.var .local (ofString "i")) (.const 136)) (.seq (.store (.op .add [(.var .local (ofString "stp")),(.var .local (ofString "i"))]) (.op .xor [(.load .one (.op .add [(.var .local (ofString "stp")),(.var .local (ofString "i"))])),(.load .one (.op .add [(.var .local (ofString "blk")),(.var .local (ofString "i"))]))])) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 8)])))) (.while (.cmp .less (.var .local (ofString "i")) (.const 136)) (.seq (.store (.op .add [(.var .local (ofString "stp")),(.var .local (ofString "i"))]) (.op .xor [(.load .one (.op .add [(.var .local (ofString "stp")),(.var .local (ofString "i"))])),(.op .or [(.loadByte (.op .add [(.var .local (ofString "blk")),(.var .local (ofString "i"))])),(.shift .lsl (.loadByte (.op .add [(.var .local (ofString "blk")),(.var .local (ofString "i")),(.const 1)])) (.const 8)),(.shift .lsl (.loadByte (.op .add [(.var .local (ofString "blk")),(.var .local (ofString "i")),(.const 2)])) (.const 16)),(.shift .lsl (.loadByte (.op .add [(.var .local (ofString "blk")),(.var .local (ofString "i")),(.const 3)])) (.const 24)),(.shift .lsl (.op .or [(.loadByte (.op .add [(.var .local (ofString "blk")),(.var .local (ofString "i")),(.const 4)])),(.shift .lsl (.loadByte (.op .add [(.var .local (ofString "blk")),(.var .local (ofString "i")),(.const 4),(.const 1)])) (.const 8)),(.shift .lsl (.loadByte (.op .add [(.var .local (ofString "blk")),(.var .local (ofString "i")),(.const 4),(.const 2)])) (.const 16)),(.shift .lsl (.loadByte (.op .add [(.var .local (ofString "blk")),(.var .local (ofString "i")),(.const 4),(.const 3)])) (.const 24))]) (.const 32))])])) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 8)]))))) (.seq (.call (some (none,none)) (ofString "keccak_f1600") [(.var .local (ofString "stp"))]) (.return (.const 0)))))

theorem source_absorb_hol : sourceFunctionBody Guest.guestFn_keccak_absorb_block = absorbHOL := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

syntax "wstep_op" ident : tactic
macro_rules
  | `(tactic| wstep_op $hwin) => `(tactic| repeat first
      | exact WStep.tail _ (by decide)
      | refine WStep.word _ _ (fun s h => ⟨_,eval_addr2 s _ _ _ (h.1.1) h.2,($hwin _ (by decide)).1⟩)
          (fun s x hx => isWord_op s _ _ x hx) ?_)

set_option maxHeartbeats 4000000 in
/-- The original `keccak_absorb_block(stp, blk)` writes only the aligned words of `[S, S + 200)` (its state), in
every outcome; the block is only read. -/
theorem keccakAbsorb_body_window {F : Type} (s : PanSemStateFiniteExact 64 F) (S Bk w : BitVec 64)
    (code : s.code = originalRuntimeCode)
    (hS : s.locals.lookup (ofString "stp") = some (.val (.word S)))
    (hB : s.locals.lookup (ofString "blk") = some (.val (.word Bk)))
    (out : ¬ MWin S 200 w) :
    (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_keccak_absorb_block)).2.memory w = s.memory w := by
  have LA := fun (t : PanSemStateFiniteExact 64 F) (inv : LoopInv (absorbP S Bk) (ofString "i") (fun I => I.toNat < 144) t) =>
    absorbLoop_window absorbAStep S Bk w (by unfold absorbAStep; adv_step)
      (fun I hwin => by unfold absorbAStep; wstep_op hwin) out t inv
  have LB := fun (t : PanSemStateFiniteExact 64 F) (inv : LoopInv (absorbP S Bk) (ofString "i") (fun I => I.toNat < 144) t) =>
    absorbLoop_window absorbBStep S Bk w (by unfold absorbBStep; adv_step)
      (fun I hwin => by unfold absorbBStep; wstep_op hwin) out t inv
  have outF : ∀ j : Nat, j < 200 → w ≠ panByteAlignHOL (S + BitVec.ofNat 64 j) := fun j hj e => out ⟨j,hj,Or.inr e⟩
  have callF : ∀ t : PanSemStateFiniteExact 64 F, t.code = originalRuntimeCode →
      t.locals.lookup (ofString "stp") = some (.val (.word S)) →
      (evaluateHOLFiniteState t (.call (some (none,none)) (ofString "keccak_f1600") [.var .local (ofString "stp")])).2.memory w =
        t.memory w := by
    intro t tc ts
    have args : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) [.var .local (ofString "stp")] =
        some [.val (.word S)] := by rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,ts]
    have lookup := pan_single_word_lookup t.code.lookup (ofString "keccak_f1600") (ofString "stp")
      (sourceFunctionBody Guest.guestFn_keccak_f1600) S (by rw [tc]; exact originalRuntimeCode_keccakF1600_lookup)
    exact (watch_discardCall t w _ _ _ args _ _ _ lookup
      ⟨keccakF_body_window _ S w (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) outF,
       keccakF_body_globals_frame _ tc⟩).1
  rw [source_absorb_hol]
  unfold absorbHOL
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · rfl
  · rename_i value hval
    split
    · have hv0 : value = .val (.word 0) := by simp [evalHOLExact] at hval; exact hval.symm
      subst hv0
      have inv0 : LoopInv (absorbP S Bk) (ofString "i") (fun I => I.toNat < 144)
          (setVarHOLFinite (ofString "i") (.val (.word 0)) s) :=
        ⟨⟨by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hS],
          by simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hB]⟩,
         0,by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],by simp⟩
      change (evaluateHOLFiniteState (setVarHOLFinite (ofString "i") (.val (.word 0)) s) _).2.memory w = s.memory w
      have branch := fun (st : ProgHOL 64)
          (L : ∀ t : PanSemStateFiniteExact 64 F, LoopInv (absorbP S Bk) (ofString "i") (fun I => I.toNat < 144) t →
            (evaluateHOLFiniteState t (.while (.cmp .less (.var .local (ofString "i")) (.const 136)) st)).2.memory w =
              t.memory w ∧
            ((evaluateHOLFiniteState t (.while (.cmp .less (.var .local (ofString "i")) (.const 136)) st)).1 = none →
              LoopInv (absorbP S Bk) (ofString "i") (fun I => I.toNat < 144)
                (evaluateHOLFiniteState t (.while (.cmp .less (.var .local (ofString "i")) (.const 136)) st)).2))
          (t : PanSemStateFiniteExact 64 F)
          (h : t.code = originalRuntimeCode ∧ LoopInv (absorbP S Bk) (ofString "i") (fun I => I.toNat < 144) t) =>
        (⟨(L t h.2).1,fun hn => ⟨(evaluateHOLFiniteState_metadata t _).1.trans h.1,((L t h.2).2 hn).1.1⟩⟩ :
          (evaluateHOLFiniteState t (.while (.cmp .less (.var .local (ofString "i")) (.const 136)) st)).2.memory w =
              t.memory w ∧
            ((evaluateHOLFiniteState t (.while (.cmp .less (.var .local (ofString "i")) (.const 136)) st)).1 = none →
              (fun r : PanSemStateFiniteExact 64 F => r.code = originalRuntimeCode ∧
                r.locals.lookup (ofString "stp") = some (.val (.word S)))
                (evaluateHOLFiniteState t (.while (.cmp .less (.var .local (ofString "i")) (.const 136)) st)).2))
      refine (seq_watch _ _ w
        (fun t => t.code = originalRuntimeCode ∧ LoopInv (absorbP S Bk) (ofString "i") (fun I => I.toNat < 144) t)
        (fun r => r.code = originalRuntimeCode ∧ r.locals.lookup (ofString "stp") = some (.val (.word S)))
        (fun _ => True)
        (ite_watch _ _ _ w
          (fun t => t.code = originalRuntimeCode ∧ LoopInv (absorbP S Bk) (ofString "i") (fun I => I.toNat < 144) t)
          (fun r => r.code = originalRuntimeCode ∧ r.locals.lookup (ofString "stp") = some (.val (.word S)))
          (branch absorbAStep LA) (branch absorbBStep LB))
        (seq_watch _ _ w
          (fun r => r.code = originalRuntimeCode ∧ r.locals.lookup (ofString "stp") = some (.val (.word S)))
          (fun _ => True) (fun _ => True)
          (fun t ⟨tc,ts⟩ => ⟨callF t tc ts,fun _ => trivial⟩)
          (fun t _ => ⟨congrFun (evaluate_readOnly_memory (.return (.const 0)) (by decide) t) w,fun _ => trivial⟩))
        (setVarHOLFinite (ofString "i") (.val (.word 0)) s) ⟨by exact code,inv0⟩).1
    · rfl

#print axioms keccakAbsorb_body_window

/-- Exact locals/globals/code frame used along straight-line code. -/
def FixR {F : Type} (Lx Gx : HolFiniteMapExact MlS (ValueHOL 64)) (t : PanSemStateFiniteExact 64 F) : Prop :=
  t.code = originalRuntimeCode ∧ t.locals = Lx ∧ t.globals = Gx

theorem storeByte_watchR {F : Type} (Lx Gx : HolFiniteMapExact MlS (ValueHOL 64)) (d v : ExpHOL 64) (w : BitVec 64)
    (hd : ∀ t : PanSemStateFiniteExact 64 F, FixR Lx Gx t → ∃ a : BitVec 64,
      @evalHOLExact 64 F _ t.toExact (fun x => Classical.propDecidable (t.memaddrs x)) d = some (.val (.word a)) ∧
        w ≠ panByteAlignHOL a)
    (t : PanSemStateFiniteExact 64 F) (r : FixR Lx Gx t) :
    (evaluateHOLFiniteState t (.storeByte d v)).2.memory w = t.memory w ∧
      ((evaluateHOLFiniteState t (.storeByte d v)).1 = none → FixR Lx Gx (evaluateHOLFiniteState t (.storeByte d v)).2) := by
  obtain ⟨a,ha,ne⟩ := hd t r
  obtain ⟨_,_,loc,glob,code,_,_⟩ := evaluate_storeByte_control_frame t d v
  exact ⟨evaluate_storeByte_memory_frame t d v a w ha ne,fun _ => ⟨code.trans r.1,loc.trans r.2.1,glob.trans r.2.2⟩⟩

theorem store_watchR {F : Type} (Lx Gx : HolFiniteMapExact MlS (ValueHOL 64)) (d v : ExpHOL 64) (w : BitVec 64)
    (hd : ∀ t : PanSemStateFiniteExact 64 F, FixR Lx Gx t → ∃ a : BitVec 64,
      @evalHOLExact 64 F _ t.toExact (fun x => Classical.propDecidable (t.memaddrs x)) d = some (.val (.word a)) ∧ w ≠ a)
    (hv : ∀ (t : PanSemStateFiniteExact 64 F) x,
      @evalHOLExact 64 F _ t.toExact (fun y => Classical.propDecidable (t.memaddrs y)) v = some x →
        ∃ y : BitVec 64, x = .val (.word y))
    (t : PanSemStateFiniteExact 64 F) (r : FixR Lx Gx t) :
    (evaluateHOLFiniteState t (.store d v)).2.memory w = t.memory w ∧
      ((evaluateHOLFiniteState t (.store d v)).1 = none → FixR Lx Gx (evaluateHOLFiniteState t (.store d v)).2) := by
  obtain ⟨a,ha,ne⟩ := hd t r
  obtain ⟨_,_,loc,glob,mem⟩ := evaluate_store_word_frame t d v a ha (hv t)
  have code := (evaluateHOLFiniteState_metadata t (.store d v)).1
  exact ⟨mem w ne,fun _ => ⟨code.trans r.1,loc.trans r.2.1,glob.trans r.2.2⟩⟩

/-- A discarded call of an installed function under the exact frame: memory at the watched word is kept if the
body keeps it from the callee entry state; normal return keeps the frame (body globals frame). -/
theorem call_watchR {F : Type} (Lx Gx : HolFiniteMapExact MlS (ValueHOL 64)) (function : MlS)
    (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64)) (w : BitVec 64)
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (_installed : originalRuntimeCode.lookup function = some (parameters,body,.one))
    (lookup : lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,.one))
    (globalsFrame : OriginalGlobalsFrame body)
    (args : ∀ t : PanSemStateFiniteExact 64 F, FixR Lx Gx t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) arguments = some values)
    (window : ∀ t : PanSemStateFiniteExact 64 F, FixR Lx Gx t →
      (evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body).2.memory w = t.memory w)
    (t : PanSemStateFiniteExact 64 F) (r : FixR Lx Gx t) :
    (evaluateHOLFiniteState t (.call (some (none,none)) function arguments)).2.memory w = t.memory w ∧
      ((evaluateHOLFiniteState t (.call (some (none,none)) function arguments)).1 = none →
        FixR Lx Gx (evaluateHOLFiniteState t (.call (some (none,none)) function arguments)).2) := by
  have lk : lookupCodeHOLFinite t.code.lookup function values = some (body,callee,.one) := by rw [r.1]; exact lookup
  have wd := watch_discardCall t w function arguments values (args t r) body callee .one lk
    ⟨window t r,globalsFrame _ (by exact r.1)⟩
  refine ⟨wd.1,fun hn => ?_⟩
  have code := (evaluateHOLFiniteState_metadata t (.call (some (none,none)) function arguments)).1
  cases run : evaluateHOLFiniteState t (.call (some (none,none)) function arguments) with
  | mk res post =>
    rw [run] at hn wd code
    subst hn
    obtain ⟨_,_,_,_,loc⟩ := evaluate_discard_normal_body_memory t post function arguments values body callee .one
      (args t r) lk run
    exact ⟨code.trans r.1,loc.trans r.2.1,wd.2.trans r.2.2⟩

#print axioms call_watchR

theorem dec_watch {F : Type} (name : MlS) (init : ExpHOL 64) (body : ProgHOL 64) (w : BitVec 64)
    (s : PanSemStateFiniteExact 64 F)
    (hb : ∀ v, @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) init = some v →
      (evaluateHOLFiniteState (setVarHOLFinite name v s) body).2.memory w = s.memory w) :
    (evaluateHOLFiniteState s (.dec name .one init body)).2.memory w = s.memory w := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · rfl
  · rename_i v hv
    split
    · exact hb v hv
    · rfl

theorem while_false {F : Type} (s : PanSemStateFiniteExact 64 F) (c : ExpHOL 64) (b : ProgHOL 64)
    (hc : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) c = some (.val (.word 0))) :
    evaluateHOLFiniteState s (.while c b) = (none,s) := by
  rw [evaluateHOLFiniteState_while_total,hc]
  simp

def keccakHOL : ProgHOL 64 := (.dec (ofString "stp") .one (.var .global (ofString "keccak_st")) (.seq (.call (some (none,none)) (ofString "memzero") [(.var .local (ofString "stp")),(.const 200)]) (.dec (ofString "i") .one (.const 0) (.seq (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [(.var .local (ofString "i")),(.const 136)])) (.seq (.call (some (none,none)) (ofString "keccak_absorb_block") [(.var .local (ofString "stp")),(.op .add [(.var .local (ofString "p")),(.var .local (ofString "i"))])]) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")),(.const 136)])))) (.dec (ofString "rem") .one (.op .sub [(.var .local (ofString "n")),(.var .local (ofString "i"))]) (.seq (.call (some (none,none)) (ofString "memzero") [(.var .global (ofString "keccak_pad")),(.const 136)]) (.seq (.call (some (none,none)) (ofString "memcpy") [(.var .global (ofString "keccak_pad")),(.op .add [(.var .local (ofString "p")),(.var .local (ofString "i"))]),(.var .local (ofString "rem"))]) (.seq (.storeByte (.op .add [(.var .global (ofString "keccak_pad")),(.var .local (ofString "rem"))]) (.const 1)) (.seq (.storeByte (.op .add [(.var .global (ofString "keccak_pad")),(.const 135)]) (.op .or [(.loadByte (.op .add [(.var .global (ofString "keccak_pad")),(.const 135)])),(.const 128)])) (.seq (.call (some (none,none)) (ofString "keccak_absorb_block") [(.var .local (ofString "stp")),(.var .global (ofString "keccak_pad"))]) (.seq (.ite (.cmp .equal (.op .and [(.var .local (ofString "out")),(.const 7)]) (.const 0)) (.seq (.store (.var .local (ofString "out")) (.load .one (.var .local (ofString "stp")))) (.seq (.store (.op .add [(.var .local (ofString "out")),(.const 8)]) (.load .one (.op .add [(.var .local (ofString "stp")),(.const 8)]))) (.seq (.store (.op .add [(.var .local (ofString "out")),(.const 16)]) (.load .one (.op .add [(.var .local (ofString "stp")),(.const 16)]))) (.store (.op .add [(.var .local (ofString "out")),(.const 24)]) (.load .one (.op .add [(.var .local (ofString "stp")),(.const 24)])))))) (.call (some (none,none)) (ofString "memcpy") [(.var .local (ofString "out")),(.var .local (ofString "stp")),(.const 32)])) (.return (.const 0)))))))))))))

theorem source_keccak_hol : sourceFunctionBody Guest.guestFn_keccak256 = keccakHOL := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl


theorem memzeroCall_watch {F : Type} (L G : HolFiniteMapExact MlS (ValueHOL 64)) (arguments : List (ExpHOL 64))
    (D Nn w : BitVec 64)
    (hargs : ∀ t : PanSemStateFiniteExact 64 F, FixR L G t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) arguments =
        some [.val (.word D),.val (.word Nn)])
    (small : Nn.toNat + 32 < 2 ^ 64) (out : ¬ MWin D Nn.toNat w) (t : PanSemStateFiniteExact 64 F) (r : FixR L G t) :
    (evaluateHOLFiniteState t (.call (some (none,none)) (ofString "memzero") arguments)).2.memory w = t.memory w ∧
      ((evaluateHOLFiniteState t (.call (some (none,none)) (ofString "memzero") arguments)).1 = none →
        FixR L G (evaluateHOLFiniteState t (.call (some (none,none)) (ofString "memzero") arguments)).2) :=
  call_watchR L G (ofString "memzero") arguments [.val (.word D),.val (.word Nn)] w _ _ _
    originalRuntimeCode_memzero_lookup
    (pan_two_word_lookup _ _ _ _ _ D Nn (by decide) originalRuntimeCode_memzero_lookup) memzero_body_globals_frame hargs
    (fun t _ => memzero_body_window _ D Nn w
      (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      small out) t r

theorem memcpyCall_watch {F : Type} (L G : HolFiniteMapExact MlS (ValueHOL 64)) (arguments : List (ExpHOL 64))
    (D S Nn w : BitVec 64)
    (hargs : ∀ t : PanSemStateFiniteExact 64 F, FixR L G t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) arguments =
        some [.val (.word D),.val (.word S),.val (.word Nn)])
    (small : Nn.toNat + 32 < 2 ^ 64) (out : ¬ MWin D Nn.toNat w) (t : PanSemStateFiniteExact 64 F) (r : FixR L G t) :
    (evaluateHOLFiniteState t (.call (some (none,none)) (ofString "memcpy") arguments)).2.memory w = t.memory w ∧
      ((evaluateHOLFiniteState t (.call (some (none,none)) (ofString "memcpy") arguments)).1 = none →
        FixR L G (evaluateHOLFiniteState t (.call (some (none,none)) (ofString "memcpy") arguments)).2) :=
  call_watchR L G (ofString "memcpy") arguments [.val (.word D),.val (.word S),.val (.word Nn)] w _ _ _
    originalRuntimeCode_memcpy_lookup
    (pan_three_word_lookup _ _ _ _ _ _ D S Nn (by decide) (by decide) (by decide) originalRuntimeCode_memcpy_lookup)
    memcpy_body_globals_frame hargs
    (fun t _ => memcpy_body_window _ D S Nn w
      (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      small out) t r

theorem absorbCall_watch {F : Type} (L G : HolFiniteMapExact MlS (ValueHOL 64)) (arguments : List (ExpHOL 64))
    (S Bk w : BitVec 64)
    (hargs : ∀ t : PanSemStateFiniteExact 64 F, FixR L G t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) arguments =
        some [.val (.word S),.val (.word Bk)])
    (out : ¬ MWin S 200 w) (t : PanSemStateFiniteExact 64 F) (r : FixR L G t) :
    (evaluateHOLFiniteState t (.call (some (none,none)) (ofString "keccak_absorb_block") arguments)).2.memory w = t.memory w ∧
      ((evaluateHOLFiniteState t (.call (some (none,none)) (ofString "keccak_absorb_block") arguments)).1 = none →
        FixR L G (evaluateHOLFiniteState t (.call (some (none,none)) (ofString "keccak_absorb_block") arguments)).2) :=
  call_watchR L G (ofString "keccak_absorb_block") arguments [.val (.word S),.val (.word Bk)] w _ _ _
    originalRuntimeCode_keccakAbsorb_lookup
    (pan_two_word_lookup _ _ _ _ _ S Bk (by decide) originalRuntimeCode_keccakAbsorb_lookup)
    keccakAbsorb_body_globals_frame hargs
    (fun t r => keccakAbsorb_body_window _ S Bk w (by exact r.1)
      (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      out) t r

theorem mwin_mono {D w : BitVec 64} {a b : Nat} (le : a ≤ b) (out : ¬ MWin D b w) : ¬ MWin D a w :=
  fun ⟨j,hj,h⟩ => out ⟨j,by omega,h⟩

#print axioms memzeroCall_watch
#print axioms memcpyCall_watch
#print axioms absorbCall_watch

theorem lk_set {L : HolFiniteMapExact MlS (ValueHOL 64)} {a b : MlS} {v x : ValueHOL 64}
    (ne : b ≠ a) (h : L.lookup b = some x) : (L.update (a,v)).lookup b = some x := by
  simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ne,h]

theorem lk_set_same {L : HolFiniteMapExact MlS (ValueHOL 64)} {a : MlS} {v : ValueHOL 64} :
    (L.update (a,v)).lookup a = some v := by
  simp [HolFiniteMapExact.lookup_update,FUPDATE]

set_option maxHeartbeats 8000000 in
/-- The original `keccak256(p, n, out)` for a short input (`n < 136`) writes only the 200-byte sponge state
`keccak_st`, the 136-byte pad `keccak_pad` and the 32 output bytes, in every outcome. -/
theorem keccak_short_body_window {F : Type} (s : PanSemStateFiniteExact 64 F) (Pp N O K Pd w : BitVec 64)
    (code : s.code = originalRuntimeCode)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word Pp)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word N)))
    (ho : s.locals.lookup (ofString "out") = some (.val (.word O)))
    (hK : s.globals.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd : s.globals.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (short : N.toNat < 136) (oK : ¬ MWin K 200 w) (oP : ¬ MWin Pd 136 w) (oO : ¬ MWin O 32 w) :
    (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_keccak256)).2.memory w = s.memory w := by
  rw [source_keccak_hol]
  unfold keccakHOL
  apply dec_watch
  intro v hv
  have vK : v = .val (.word K) := by simp [evalHOLExact,hK] at hv; exact hv.symm
  subst vK
  generalize hL1 : (setVarHOLFinite (ofString "stp") (.val (.word K)) s).locals = L1
  have l1stp : L1.lookup (ofString "stp") = some (.val (.word K)) := by
    rw [← hL1]; exact lk_set_same
  have l1p : L1.lookup (ofString "p") = some (.val (.word Pp)) := by rw [← hL1]; exact lk_set (by decide) hp
  have l1n : L1.lookup (ofString "n") = some (.val (.word N)) := by rw [← hL1]; exact lk_set (by decide) hn
  have l1o : L1.lookup (ofString "out") = some (.val (.word O)) := by rw [← hL1]; exact lk_set (by decide) ho
  refine (seq_watch _ _ w (FixR L1 s.globals) (FixR L1 s.globals) (fun _ => True)
    (memzeroCall_watch L1 s.globals _ K 200 w (fun t r => by
      rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,r.2.1,l1stp]) (by decide) oK) ?_
    (setVarHOLFinite (ofString "stp") (.val (.word K)) s) ⟨by exact code,hL1,rfl⟩).1
  intro t r
  refine ⟨?_,fun _ => trivial⟩
  apply dec_watch
  intro v hv
  have v0 : v = .val (.word 0) := by simp [evalHOLExact] at hv; exact hv.symm
  subst v0
  have tn : (setVarHOLFinite (ofString "i") (.val (.word 0)) t).locals.lookup (ofString "n") = some (.val (.word N)) := by
    simp only [setVarHOLFinite]; rw [r.2.1]; exact lk_set (by decide) l1n
  have ti : (setVarHOLFinite (ofString "i") (.val (.word 0)) t).locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp only [setVarHOLFinite]; exact lk_set_same
  have tm : (setVarHOLFinite (ofString "i") (.val (.word 0)) t).memory = t.memory := rfl
  have tl : (setVarHOLFinite (ofString "i") (.val (.word 0)) t).locals =
      (t.locals.update (ofString "i",.val (.word 0))) := rfl
  have tg : (setVarHOLFinite (ofString "i") (.val (.word 0)) t).globals = t.globals := rfl
  have tc : (setVarHOLFinite (ofString "i") (.val (.word 0)) t).code = t.code := rfl
  generalize (setVarHOLFinite (ofString "i") (.val (.word 0)) t) = t2 at tn ti tm tl tg tc ⊢
  have cond : evalHOLFinite t2 (h := fun a => Classical.propDecidable (t2.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"),.const 136])) =
        some (.val (.word 0)) := by
    rw [evalHOLFinite_eq_toExact]
    simp [evalHOLExact,evalListHOLExact,tn,ti,wordOpHOL,wordOp,valueIsWord,valueWord,Compiler.Encoders.Asm.wordCmpHOL]
    rw [BitVec.lt_def]
    have : (136#64).toNat = 136 := rfl
    omega
  rw [evaluateHOLFiniteState_seq_line780,while_false _ _ _ cond]
  dsimp only
  rw [← tm]
  apply dec_watch
  intro v hv
  have vN : v = .val (.word N) := by
    simp [evalHOLExact,evalListHOLExact,tn,ti,wordOpHOL,wordOp,valueIsWord,valueWord] at hv; exact hv.symm
  subst vN
  have G0 : t2.globals = s.globals := tg.trans r.2.2
  have C0 : t2.code = originalRuntimeCode := tc.trans r.1
  generalize hL3 : (setVarHOLFinite (ofString "rem") (.val (.word N)) t2).locals = L3
  have l3 : ∀ (x : MlS) (y : Option (ValueHOL 64)), x ≠ ofString "rem" → x ≠ ofString "i" → L1.lookup x = y → L3.lookup x = y := by
    intro x y h1 h2 h
    rw [← hL3]; simp only [setVarHOLFinite]; rw [tl,r.2.1]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm h1,Ne.symm h2,h]
  have l3stp := l3 _ _ (by decide) (by decide) l1stp
  have l3p := l3 _ _ (by decide) (by decide) l1p
  have l3o := l3 _ _ (by decide) (by decide) l1o
  have l3i : L3.lookup (ofString "i") = some (.val (.word 0)) := by
    rw [← hL3]; simp only [setVarHOLFinite]; rw [tl]
    have : ofString "rem" ≠ ofString "i" := by decide
    simp [HolFiniteMapExact.lookup_update,FUPDATE,this]
  have l3rem : L3.lookup (ofString "rem") = some (.val (.word N)) := by
    rw [← hL3]; simp only [setVarHOLFinite]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have r3 : FixR L3 s.globals (setVarHOLFinite (ofString "rem") (.val (.word N)) t2) := ⟨C0,hL3,G0⟩
  have padOut : ∀ j : Nat, j < 136 → w ≠ panByteAlignHOL (Pd + BitVec.ofNat 64 j) ∧ w ≠ Pd + BitVec.ofNat 64 j :=
    fun j hj => ⟨fun e => oP ⟨j,hj,Or.inr e⟩,fun e => oP ⟨j,hj,Or.inl e⟩⟩
  have outOut : ∀ j : Nat, j < 32 → w ≠ O + BitVec.ofNat 64 j := fun j hj e => oO ⟨j,hj,Or.inl e⟩
  have tm' : (setVarHOLFinite (ofString "rem") (.val (.word N)) t2).memory = t2.memory := rfl
  rw [← tm']
  refine (seq_watch _ _ w (FixR L3 s.globals) (FixR L3 s.globals) (fun _ => True)
    (memzeroCall_watch L3 s.globals _ Pd 136 w (fun t r => by
      rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,r.2.2,hPd]) (by decide) oP) ?_ _ r3).1
  intro u1 r1
  refine ⟨(seq_watch _ _ w (FixR L3 s.globals) (FixR L3 s.globals) (fun _ => True)
    (memcpyCall_watch L3 s.globals _ Pd (Pp + 0) N w (fun t r => by
      rw [evalListHOLFinite_eq_toExact]
      simp [evalListHOLExact,evalHOLExact,r.2.1,r.2.2,hPd,l3p,l3i,l3rem,wordOpHOL,wordOp,valueIsWord,valueWord])
      (by omega) (mwin_mono (by omega) oP)) ?_ u1 r1).1,fun _ => trivial⟩
  intro u2 r2
  refine ⟨(seq_watch _ _ w (FixR L3 s.globals) (FixR L3 s.globals) (fun _ => True)
    (storeByte_watchR L3 s.globals _ _ w (fun t r => ⟨Pd + N,by
      simp [evalHOLExact,evalListHOLExact,r.2.1,r.2.2,hPd,l3rem,wordOpHOL,wordOp,valueIsWord,valueWord],by
      have e : Pd + N = Pd + BitVec.ofNat 64 N.toNat := by simp
      rw [e]; exact (padOut _ short).1⟩)) ?_ u2 r2).1,fun _ => trivial⟩
  intro u3 r3'
  refine ⟨(seq_watch _ _ w (FixR L3 s.globals) (FixR L3 s.globals) (fun _ => True)
    (storeByte_watchR L3 s.globals _ _ w (fun t r => ⟨Pd + 135,by
      simp [evalHOLExact,evalListHOLExact,r.2.2,hPd,wordOpHOL,wordOp,valueIsWord,valueWord],
      (padOut 135 (by decide)).1⟩)) ?_ u3 r3').1,fun _ => trivial⟩
  intro u4 r4
  refine ⟨(seq_watch _ _ w (FixR L3 s.globals) (FixR L3 s.globals) (fun _ => True)
    (absorbCall_watch L3 s.globals _ K Pd w (fun t r => by
      rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,r.2.1,r.2.2,hPd,l3stp]) oK) ?_ u4 r4).1,
    fun _ => trivial⟩
  intro u5 r5
  have st : ∀ (c : BitVec 64) (j : Nat), c = BitVec.ofNat 64 j → j < 32 → ∀ t : PanSemStateFiniteExact 64 F,
      FixR L3 s.globals t → ∃ a : BitVec 64,
        @evalHOLExact 64 F _ t.toExact (fun x => Classical.propDecidable (t.memaddrs x))
          (.op .add [.var .local (ofString "out"),.const c]) = some (.val (.word a)) ∧ w ≠ a := by
    intro c j hc hj t r
    refine ⟨O + c,by simp [evalHOLExact,evalListHOLExact,r.2.1,l3o,wordOpHOL,wordOp,valueIsWord,valueWord],?_⟩
    rw [hc]; exact outOut j hj
  refine ⟨(seq_watch _ _ w (FixR L3 s.globals) (FixR L3 s.globals) (fun _ => True)
    (ite_watch _ _ _ w (FixR L3 s.globals) (FixR L3 s.globals)
      (seq_watch _ _ w (FixR L3 s.globals) (FixR L3 s.globals) (FixR L3 s.globals)
        (store_watchR L3 s.globals _ _ w (fun t r => ⟨O,by simp [evalHOLExact,r.2.1,l3o],
          by simpa using outOut 0 (by decide)⟩) (fun t x hx => isWord_load t _ x hx))
        (seq_watch _ _ w (FixR L3 s.globals) (FixR L3 s.globals) (FixR L3 s.globals)
          (store_watchR L3 s.globals _ _ w (st 8 8 rfl (by decide)) (fun t x hx => isWord_load t _ x hx))
          (seq_watch _ _ w (FixR L3 s.globals) (FixR L3 s.globals) (FixR L3 s.globals)
            (store_watchR L3 s.globals _ _ w (st 16 16 rfl (by decide)) (fun t x hx => isWord_load t _ x hx))
            (store_watchR L3 s.globals _ _ w (st 24 24 rfl (by decide)) (fun t x hx => isWord_load t _ x hx)))))
      (memcpyCall_watch L3 s.globals _ O K 32 w (fun t r => by
        rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,r.2.1,l3o,l3stp]) (by decide) oO))
    (fun t _ => ⟨congrFun (evaluate_readOnly_memory (.return (.const 0)) (by decide) t) w,fun _ => trivial⟩)
    u5 r5).1,fun _ => trivial⟩

#print axioms keccak_short_body_window
end InitECandidate.Runtime
