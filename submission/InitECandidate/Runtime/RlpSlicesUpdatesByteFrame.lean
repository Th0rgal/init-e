import InitECandidate.Runtime.RlpSlicesStoredEntry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual slice entry stores preserve byte reads whose containing word is
separate from the two destination cells. -/
theorem rlpSlices_updates_byte_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array index pointer offset total : BitVec 64)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (offsetLocal : state.locals.lookup (ofString "off") = some (.val (.word offset)))
    (totalLocal : state.locals.lookup (ofString "total") = some (.val (.word total)))
    (domain0 : state.memaddrs (array + index * 16#64))
    (domain8 : state.memaddrs (array + index * 16#64 + 8#64))
    (run : evaluateHOLFiniteState state rlpSlicesUpdates = (none,post))
    (address : BitVec 64)
    (different0 : panByteAlignHOL address ≠ array + index * 16#64)
    (different8 : panByteAlignHOL address ≠ array + index * 16#64 + 8#64) :
    @panMemLoadByteHOL 64 _ post.memory post.memaddrs
      (fun address => Classical.propDecidable (post.memaddrs address)) post.be address =
    @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be address := by
  obtain ⟨output,evaluated,_,_,domain,frame⟩ := evaluate_rlpSlices_updates_entry_frame state array index pointer offset total
    arrayLocal indexLocal pointerLocal offsetLocal totalLocal domain0 domain8
  have equal : output = post := (Prod.mk.inj (evaluated.symm.trans run)).2
  subst output
  have metadata := evaluateHOLFiniteState_metadata state rlpSlicesUpdates
  rw [run] at metadata
  dsimp only at metadata
  have endian := metadata.2.2.1
  have cell := frame (panByteAlignHOL address) different0 different8
  by_cases accessible : state.memaddrs (panByteAlignHOL address)
  · have afterAccessible : post.memaddrs (panByteAlignHOL address) := by rw [domain]; exact accessible
    simp [panMemLoadByteHOL,accessible,afterAccessible,endian,cell]
  · have afterInaccessible : ¬post.memaddrs (panByteAlignHOL address) := by rw [domain]; exact accessible
    simp [panMemLoadByteHOL,accessible,afterInaccessible]

#print axioms rlpSlices_updates_byte_frame
end InitECandidate.Runtime
