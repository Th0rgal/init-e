import InitECandidate.Runtime.MerkleLevelBound
import InitECandidate.Runtime.LocalBoundLoop
import InitECandidate.Runtime.RunBounded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- With the actual chunk count available, a Merkle level costs at most
137 ticks per current chunk, rather than the uniform 64-bit fallback. -/
theorem runBounded_merkleLevel {F : Type} (state : PanSemStateFiniteExact 64 F)
    (cur : BitVec 64) (counter : state.locals.lookup (ofString "cur") = some (.val (.word cur)))
    (small : cur.toNat < 2 ^ 63) (code : state.code = originalRuntimeCode)
    (budget : cur.toNat * 137 ≤ state.clock) :
    RunBounded state merkleLevelBody (cur.toNat * 137) := by
  have natural : (cur >>> 1).toNat = cur.toNat / 2 := by
    simp [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  have initialized : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.shift .lsr (.var .local (ofString "cur")) (.const 1)) = some (.val (.word (cur >>> 1))) := by
    simp [evalHOLExact,counter,wordShiftHOL]
  rw [source_merkleLevel_body]
  apply RunBounded.decWord state (ofString "half") _ (cur >>> 1) initialized
  apply RunBounded.decConst
  generalize hentry : setVarHOLFinite (ofString "j") (.val (.word (0#64)))
      (setVarHOLFinite (ofString "half") (.val (.word (cur >>> 1))) state) = entry
  have entryClock : entry.clock = state.clock := by rw [← hentry]; rfl
  have entryCode : entry.code = originalRuntimeCode := by rw [← hentry]; exact code
  have atCounter : entry.locals.lookup (ofString "j") = some (.val (.word (0#64))) := by
    rw [← hentry]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atHalf : entry.locals.lookup (ofString "half") = some (.val (.word (cur >>> 1))) := by
    rw [← hentry]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "j" ≠ ofString "half" by decide]
  have loop := localBoundWhile_run (ofString "j") (ofString "half") 1 (cur >>> 1)
    (LocalBoundTest.below .less (Or.inl rfl))
    (by rw [natural]; change cur.toNat / 2 + 1 < 2 ^ 63; omega)
    (by decide) merklePair_counted (by decide) (by decide) entry entryCode 0 atCounter atHalf
    (by decide) (by simp; rw [Nat.shiftRight_eq_div_pow,entryClock]; omega)
  have loopBound : RunBounded entry merklePairLoop ((cur >>> 1).toNat * 137) := by
    exact ⟨by simpa [merklePairLoop] using loop.1,by simpa [merklePairLoop] using loop.2.1,
      by simpa [merklePairLoop] using loop.2.2.1⟩
  apply RunBounded.weaken (cost := (cur >>> 1).toNat * 137 + 0)
  · refine RunBounded.seq loopBound (by rw [natural,entryClock]; omega) ?_
    intro next _ nextCode _
    exact RunBounded.ofProg (ProgBounded.straight _ (by decide)) (nextCode.trans entryCode) (Nat.zero_le _)
  · rw [natural]
    omega

#print axioms runBounded_merkleLevel
end InitECandidate.Runtime
