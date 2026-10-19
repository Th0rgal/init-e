import InitECandidate.Runtime.CompactNibblePrefixNormalFrame
import InitECandidate.Runtime.CompactNibbleFinishUniformBound
import InitECandidate.Runtime.CompactNibbleAfterAlloc
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual post-allocation compact decoder is bounded without assuming its
optional first-byte write or later conversion accesses succeed. -/
theorem runBounded_compact_nibble_after_alloc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer length out c0 odd : BitVec 64)
    (small : (length - 1).toNat + 4 < 2^64)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atOut : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (atByte : s.locals.lookup (ofString "c0") = some (.val (.word c0)))
    (atOdd : s.locals.lookup (ofString "odd") = some (.val (.word odd)))
    (code : s.code = originalRuntimeCode) (ticks : (length - 1).toNat / 4 + 4 ≤ s.clock) :
    RunBounded s compactNibbleAfterAlloc ((length - 1).toNat / 4 + 4) := by
  rw [source_compactNibble_after_alloc]
  apply RunBounded.decConst
  let entered := setVarHOLFinite (ofString "k") (.val (.word (0 : BitVec 64))) s
  have others : ∀ name, name ≠ ofString "k" → entered.locals.lookup name = s.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have counter : entered.locals.lookup (ofString "k") = some (.val (.word (0 : BitVec 64))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have prefixBound : RunBounded entered compactNibblePrefix 0 :=
    RunBounded.ofProg (ProgBounded.straight _ (by rw [source_compactNibble_prefix]; rfl)) code (by omega)
  suffices RunBounded entered (.seq compactNibblePrefix compactNibbleFinish)
      (0 + ((length - 1).toNat / 4 + 4)) by simpa only [Nat.zero_add,entered] using this
  apply RunBounded.seq prefixBound (by change 0 + ((length - 1).toNat / 4 + 4) ≤ s.clock; omega)
  intro next normal nextCode budget
  obtain ⟨atCounter,locals⟩ := compact_nibble_prefix_normal_frame entered next out c0 odd
    ((others _ (by decide)).trans atOut) ((others _ (by decide)).trans atByte)
    ((others _ (by decide)).trans atOdd) counter normal
  exact runBounded_compact_nibble_finish next pointer length out (if odd = 0 then 0 else 1) small
    ((locals _ (by decide)).trans ((others _ (by decide)).trans atPointer))
    ((locals _ (by decide)).trans ((others _ (by decide)).trans atLength))
    ((locals _ (by decide)).trans ((others _ (by decide)).trans atOut)) atCounter
    (nextCode.trans code) budget

#print axioms runBounded_compact_nibble_after_alloc
end InitECandidate.Runtime
