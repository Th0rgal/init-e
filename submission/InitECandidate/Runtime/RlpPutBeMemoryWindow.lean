import InitECandidate.Runtime.RlpHeaderLenMemoryFrame
import InitECandidate.Runtime.StoreLoopWindow
import InitECandidate.Runtime.ByteStoreMemoryFrame
import InitECandidate.Runtime.ByteStoresControlFrame
import InitECandidate.Runtime.LocalAssignNormalValue
import InitECandidate.Runtime.AccountLeafWindow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- One iteration of the `rlp_put_be` byte countdown: `i := i - 1; storeByte (dst + i) v; v := v >>> 8`. -/
def rlpPutBeStep : ProgHOL 64 :=
  .seq (.assign .local (ofString "i") (.op .sub [.var .local (ofString "i"), .const (1#64)]))
    (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
        (.var .local (ofString "v")))
      (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const (8#64)))))

/-- The countdown loop of `rlp_put_be`: `while 0 < i { i := i - 1; storeByte (dst + i) v; v := v >>> 8 }`. -/
def rlpPutBeLoop : ProgHOL 64 :=
  .while (.cmp .lower (.const (0#64)) (.var .local (ofString "i"))) rlpPutBeStep

/-- The index subtraction `I - 1` of one iteration, with its exact value. -/
theorem rlpPutBe_sub_one {I : BitVec 64} (hpos : 0 < I.toNat) :
    ((I - 1#64)).toNat + 1 = I.toNat := by
  have hpos' : 1 ≤ I.toNat := by omega
  have hI : (1 : BitVec 64) ≤ I := BitVec.le_def.mpr (by simpa using hpos')
  have h := BitVec.toNat_sub_of_le (n := 64) (x := I) (y := (1#64)) hI
  have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
  omega

#print axioms rlpPutBe_sub_one

/-- Reading back the variable just written by a local assignment. -/
theorem lookup_setVar_eq {F : Type} (s : PanSemStateFiniteExact 64 F) (name : MlS)
    (v : ValueHOL 64) :
    (setVarHOLFinite name v s).locals.lookup name = some v := by
  simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms lookup_setVar_eq

/-- A local assignment leaves every other variable readable as before. -/
theorem lookup_setVar_ne {F : Type} (s : PanSemStateFiniteExact 64 F) (name other : MlS)
    (v x : ValueHOL 64) (ne : name ≠ other) (h : s.locals.lookup other = some x) :
    (setVarHOLFinite name v s).locals.lookup other = some x := by
  simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ne,h]

#print axioms lookup_setVar_ne

/-- One `rlp_put_be` iteration writes only at `dst + (I-1)`, which lies inside `[D, D+N)` when the
countdown index is `I` with `0 < I ≤ N`.  Hence every word outside that window keeps its cell, in every
outcome of the iteration (normal completion, store error, index error). -/
theorem rlpPutBeStep_memory {F : Type} (s : PanSemStateFiniteExact 64 F) (D N w I : BitVec 64)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word D)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word I)))
    (out : ¬ MWin D N.toNat w) (hpos : 0 < I.toNat) (hIN : I.toNat ≤ N.toNat) :
    (evaluateHOLFiniteState s rlpPutBeStep).2.memory w = s.memory w := by
  have bound : ((I - 1#64)).toNat + (0#64).toNat < N.toNat := by
    have h := rlpPutBe_sub_one hpos
    have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
    omega
  have sepRaw := (mwin_off (D := D) (I := I - 1#64) (c := 0#64) (w := w) (N := N.toNat) out bound).2
  have sep : w ≠ panByteAlignHOL (D + (I - 1#64)) := by simpa using sepRaw
  have memA : ∀ {F' : Type} (t : PanSemStateFiniteExact 64 F'),
      (evaluateHOLFiniteState t (.assign .local (ofString "i")
        (.op .sub [.var .local (ofString "i"), .const (1#64)]))).2.memory w = t.memory w :=
    fun t => congrFun (evaluate_assign_memory t .local (ofString "i")
      (.op .sub [.var .local (ofString "i"), .const (1#64)])) w
  unfold rlpPutBeStep
  rw [evaluateHOLFiniteState_seq_line780]
  dsimp only
  cases hA : evaluateHOLFiniteState s (.assign .local (ofString "i")
    (.op .sub [.var .local (ofString "i"), .const (1#64)])) with
  | mk rA sA =>
  dsimp only
  have memsA : sA.memory w = s.memory w := by
    have := memA s
    rwa [hA] at this
  cases rA with
  | some e => exact memsA
  | none =>
    obtain ⟨valueA, evalA, sAeq⟩ := evaluate_local_assign_normal_value s sA (ofString "i")
      (.op .sub [.var .local (ofString "i"), .const (1#64)]) hA
    have evalI : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.op .sub [.var .local (ofString "i"), .const (1#64)]) = some (.val (.word (I - 1#64))) := by
      simp [evalListHOLExact,evalHOLExact,hi,wordOpHOL,wordOp,valueIsWord,valueWord]
    rw [evalI] at evalA
    have valueEq : valueA = .val (.word (I - 1#64)) := (Option.some.inj evalA).symm
    rw [valueEq] at sAeq
    have hsAdst : sA.locals.lookup (ofString "dst") = some (.val (.word D)) := by
      rw [sAeq]
      exact lookup_setVar_ne s (ofString "i") (ofString "dst") _ _ (by decide) hd
    have hsAi : sA.locals.lookup (ofString "i") = some (.val (.word (I - 1#64))) := by
      rw [sAeq]
      exact lookup_setVar_eq s (ofString "i") _
    have addrEval : @evalHOLExact 64 F _ sA.toExact
        (fun a => Classical.propDecidable (sA.memaddrs a))
        (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) =
        some (.val (.word (D + (I - 1#64)))) := by
      simp [evalListHOLExact,evalHOLExact,hsAdst,hsAi,wordOpHOL,wordOp,valueIsWord,valueWord]
    have storeMem : (evaluateHOLFiniteState sA (.storeByte
        (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
        (.var .local (ofString "v")))).2.memory w = sA.memory w :=
      evaluate_storeByte_memory_frame sA _ _ (D + (I - 1#64)) w addrEval sep
    rw [evaluateHOLFiniteState_seq_line780]
    dsimp only
    cases hB : evaluateHOLFiniteState sA (.storeByte
      (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
      (.var .local (ofString "v"))) with
    | mk rB sB =>
    dsimp only
    have memsB : sB.memory w = sA.memory w := by
      have := storeMem
      rwa [hB] at this
    cases rB with
    | some e => exact memsB.trans memsA
    | none =>
      exact (congrFun (evaluate_assign_memory sB .local (ofString "v")
        (.shift .lsr (.var .local (ofString "v")) (.const (8#64)))) w).trans (memsB.trans memsA)

#print axioms rlpPutBeStep_memory

end InitECandidate.Runtime
