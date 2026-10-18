import InitECandidate.Runtime.DecodeBytesListBody
import InitECandidate.Runtime.PanFourWordShapeLookup
import InitECandidate.Runtime.PanDecCallStraightBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A byte-list declaration with a straight-line continuation includes
all decoder rejection paths in its input-length clock bound. -/
theorem evaluate_decodeBytesList_declaration_straight_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (continuation : ProgHOL 64) (supported : straightLine continuation = true)
    (arguments : List (ExpHOL 64))
    (pointer length limit maxBytes heapPointer : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length),.val (.word limit),.val (.word maxBytes)])
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (budget : bytesListBound length + 1 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.decCall name (.comb [.one,.one]) (ofString "decode_bytes_list") arguments continuation)
    state.clock ≤ evaluated.2.clock + (bytesListBound length + 1) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (((HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update
      (ofString "len",.val (.word length))).update (ofString "lim",.val (.word limit))).update
      (ofString "maxb",.val (.word maxBytes))
  let entry := callEntryStateHOLFinite state callee
  have p : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide,show ofString "lim" ≠ ofString "p" by decide,
      show ofString "maxb" ≠ ofString "p" by decide]
  have len : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "lim" ≠ ofString "len" by decide,show ofString "maxb" ≠ ofString "len" by decide]
  have lim : entry.locals.lookup (ofString "lim") = some (.val (.word limit)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "maxb" ≠ ofString "lim" by decide]
  have maxb : entry.locals.lookup (ofString "maxb") = some (.val (.word maxBytes)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have bounded := evaluate_decodeBytesList_body entry pointer length limit maxBytes heapPointer code p len lim maxb heap heapBound
  have lookup := pan_four_word_shape_lookup state.code.lookup (ofString "decode_bytes_list")
    (ofString "p") (ofString "len") (ofString "lim") (ofString "maxb")
    (sourceFunctionBody Guest.guestFn_decode_bytes_list) (.comb [.one,.one]) pointer length limit maxBytes
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [code]; exact originalRuntimeCode_decodeBytesList_lookup)
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_decode_bytes_list) with
  | mk result post =>
    rw [bodyRun] at bounded
    dsimp only at bounded
    exact evaluate_decCall_straight_bounded state post name (ofString "decode_bytes_list")
      (.comb [.one,.one]) (.comb [.one,.one]) arguments
      [.val (.word pointer),.val (.word length),.val (.word limit),.val (.word maxBytes)]
      (sourceFunctionBody Guest.guestFn_decode_bytes_list) continuation callee result (bytesListBound length + 1)
      args lookup (by omega) bodyRun bounded.2.1
      (by have consumed := bounded.1; change state.clock - 1 ≤ post.clock + bytesListBound length at consumed; omega)
      (bounded.2.2.1 (by change bytesListBound length ≤ state.clock - 1; omega)) supported

#print axioms evaluate_decodeBytesList_declaration_straight_bounded
end InitECandidate.Runtime
