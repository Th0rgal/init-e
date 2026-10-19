import InitECandidate.Runtime.KeccakWindow
import InitECandidate.Runtime.KeccakZeroPrefixes
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- The post-loop remainder hash writes only the state, pad and output windows,
for any source offset and every outcome, including memory and external failures. -/
theorem keccak_general_remainder_window {F : Type} (s : PanSemStateFiniteExact 64 F) (Pp Index N O K Pd w : BitVec 64)
    (code : s.code = originalRuntimeCode)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word Pp)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word Index)))
    (hRem : s.locals.lookup (ofString "rem") = some (.val (.word N)))
    (ho : s.locals.lookup (ofString "out") = some (.val (.word O)))
    (hStp : s.locals.lookup (ofString "stp") = some (.val (.word K)))
    (hPd : s.globals.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (short : N.toNat < 136) (oK : ¬ MWin K 200 w) (oP : ¬ MWin Pd 136 w) (oO : ¬ MWin O 32 w) :
    (evaluateHOLFiniteState s keccakRemainderTail).2.memory w = s.memory w := by
  unfold keccakRemainderTail
  rw [source_keccak_hol]
  simp only [keccakHOL,stateInitSpineDrop]
  have r3 : FixR s.locals s.globals s := ⟨code,rfl,rfl⟩
  have padOut : ∀ j : Nat, j < 136 → w ≠ panByteAlignHOL (Pd + BitVec.ofNat 64 j) ∧ w ≠ Pd + BitVec.ofNat 64 j :=
    fun j hj => ⟨fun e => oP ⟨j,hj,Or.inr e⟩,fun e => oP ⟨j,hj,Or.inl e⟩⟩
  have outOut : ∀ j : Nat, j < 32 → w ≠ O + BitVec.ofNat 64 j := fun j hj e => oO ⟨j,hj,Or.inl e⟩
  refine (seq_watch _ _ w (FixR s.locals s.globals) (FixR s.locals s.globals) (fun _ => True)
    (memzeroCall_watch s.locals s.globals _ Pd 136 w (fun t r => by
      rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,r.2.2,hPd]) (by decide) oP) ?_ _ r3).1
  intro u1 r1
  refine ⟨(seq_watch _ _ w (FixR s.locals s.globals) (FixR s.locals s.globals) (fun _ => True)
    (memcpyCall_watch s.locals s.globals _ Pd (Pp + Index) N w (fun t r => by
      rw [evalListHOLFinite_eq_toExact]
      simp [evalListHOLExact,evalHOLExact,r.2.1,r.2.2,hPd,hp,hi,hRem,wordOpHOL,wordOp,valueIsWord,valueWord])
      (by omega) (mwin_mono (by omega) oP)) ?_ u1 r1).1,fun _ => trivial⟩
  intro u2 r2
  refine ⟨(seq_watch _ _ w (FixR s.locals s.globals) (FixR s.locals s.globals) (fun _ => True)
    (storeByte_watchR s.locals s.globals _ _ w (fun t r => ⟨Pd + N,by
      simp [evalHOLExact,evalListHOLExact,r.2.1,r.2.2,hPd,hRem,wordOpHOL,wordOp,valueIsWord,valueWord],by
      have e : Pd + N = Pd + BitVec.ofNat 64 N.toNat := by simp
      rw [e]; exact (padOut _ short).1⟩)) ?_ u2 r2).1,fun _ => trivial⟩
  intro u3 r3'
  refine ⟨(seq_watch _ _ w (FixR s.locals s.globals) (FixR s.locals s.globals) (fun _ => True)
    (storeByte_watchR s.locals s.globals _ _ w (fun t r => ⟨Pd + 135,by
      simp [evalHOLExact,evalListHOLExact,r.2.2,hPd,wordOpHOL,wordOp,valueIsWord,valueWord],
      (padOut 135 (by decide)).1⟩)) ?_ u3 r3').1,fun _ => trivial⟩
  intro u4 r4
  refine ⟨(seq_watch _ _ w (FixR s.locals s.globals) (FixR s.locals s.globals) (fun _ => True)
    (absorbCall_watch s.locals s.globals _ K Pd w (fun t r => by
      rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,r.2.1,r.2.2,hPd,hStp]) oK) ?_ u4 r4).1,
    fun _ => trivial⟩
  intro u5 r5
  have st : ∀ (c : BitVec 64) (j : Nat), c = BitVec.ofNat 64 j → j < 32 → ∀ t : PanSemStateFiniteExact 64 F,
      FixR s.locals s.globals t → ∃ a : BitVec 64,
        @evalHOLExact 64 F _ t.toExact (fun x => Classical.propDecidable (t.memaddrs x))
          (.op .add [.var .local (ofString "out"),.const c]) = some (.val (.word a)) ∧ w ≠ a := by
    intro c j hc hj t r
    refine ⟨O + c,by simp [evalHOLExact,evalListHOLExact,r.2.1,ho,wordOpHOL,wordOp,valueIsWord,valueWord],?_⟩
    rw [hc]; exact outOut j hj
  refine ⟨(seq_watch _ _ w (FixR s.locals s.globals) (FixR s.locals s.globals) (fun _ => True)
    (ite_watch _ _ _ w (FixR s.locals s.globals) (FixR s.locals s.globals)
      (seq_watch _ _ w (FixR s.locals s.globals) (FixR s.locals s.globals) (FixR s.locals s.globals)
        (store_watchR s.locals s.globals _ _ w (fun t r => ⟨O,by simp [evalHOLExact,r.2.1,ho],
          by simpa using outOut 0 (by decide)⟩) (fun t x hx => isWord_load t _ x hx))
        (seq_watch _ _ w (FixR s.locals s.globals) (FixR s.locals s.globals) (FixR s.locals s.globals)
          (store_watchR s.locals s.globals _ _ w (st 8 8 rfl (by decide)) (fun t x hx => isWord_load t _ x hx))
          (seq_watch _ _ w (FixR s.locals s.globals) (FixR s.locals s.globals) (FixR s.locals s.globals)
            (store_watchR s.locals s.globals _ _ w (st 16 16 rfl (by decide)) (fun t x hx => isWord_load t _ x hx))
            (store_watchR s.locals s.globals _ _ w (st 24 24 rfl (by decide)) (fun t x hx => isWord_load t _ x hx)))))
      (memcpyCall_watch s.locals s.globals _ O K 32 w (fun t r => by
        rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact,evalHOLExact,r.2.1,ho,hStp]) (by decide) oO))
    (fun t _ => ⟨congrFun (evaluate_readOnly_memory (.return (.const 0)) (by decide) t) w,fun _ => trivial⟩)
    u5 r5).1,fun _ => trivial⟩

#print axioms keccak_general_remainder_window
end InitECandidate.Runtime
