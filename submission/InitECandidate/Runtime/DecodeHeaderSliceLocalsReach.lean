import InitECandidate.Runtime.DecodeHeaderListEntryReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original two projection declarations bind the actual returned slice
array/count without changing memory, globals or clock. -/
theorem decode_header_slice_locals_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count : BitVec 64)
    (atList : s.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)])) :
    Reaches s (decodeHeaderAt 3)
      (fun post => post = setVarHOLFinite (ofString "n") (.val (.word count))
        (setVarHOLFinite (ofString "arr") (.val (.word array)) s))
      0 (decodeHeaderAt 5) := by
  let first := setVarHOLFinite (ofString "arr") (.val (.word array)) s
  have start : Reaches s (decodeHeaderAt 3) (fun next => next = first) 0 (decodeHeaderAt 4) := by
    rw [source_decode_header_array]
    apply reaches_dec
    intro value evaluated
    have same : value = .val (.word array) := by simpa [evalHOLExact,atList] using evaluated.symm
    subst value
    exact ⟨array,rfl,rfl⟩
  apply reaches_trans s (decodeHeaderAt 3) (decodeHeaderAt 4) (decodeHeaderAt 5) _ _ 0 0 start
  intro next same
  subst next
  rw [source_decode_header_count_local]
  apply reaches_dec
  intro value evaluated
  have listKept : first.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)]) := by
    simpa (config := {decide := true}) [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atList
  have same : value = .val (.word count) := by simpa [evalHOLExact,listKept] using evaluated.symm
  subst value
  exact ⟨count,rfl,rfl⟩

#print axioms decode_header_slice_locals_reaches
end InitECandidate.Runtime
