import InitECandidate.Runtime.ByteOffsetStorePlanMemory
import InitECandidate.Runtime.BigEndianGlobalsFrame
import InitECandidate.Runtime.MerkleizeSource
import InitECandidate.Runtime.PanDiscardCallNormalResult
import InitECandidate.Runtime.PanTwoWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def storeBE32ByteStores : List (Nat × ExpHOL 64) :=
  [(0,.shift .lsr (.var .local (ofString "v")) (.const 24)),
   (1,.shift .lsr (.var .local (ofString "v")) (.const 16)),
   (2,.shift .lsr (.var .local (ofString "v")) (.const 8)),
   (3,.var .local (ofString "v"))]

theorem source_storeBE32_byte_plan : sourceFunctionBody Guest.guestFn_st_be32 =
    byteOffsetStorePlan (ofString "p") storeBE32ByteStores (.return (.const 0)) := by
  rw [sourceFunctionBody_eq_structural]; rfl

theorem storeBE32_body_memory {F : Type} (state : PanSemStateFiniteExact 64 F) (pointer watched : BitVec 64)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (separate : ∀ offset : Nat, offset < 4 → watched ≠ panByteAlignHOL (pointer + BitVec.ofNat 64 offset)) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_st_be32)).2.memory watched = state.memory watched := by
  rw [source_storeBE32_byte_plan]
  apply byteOffsetStorePlan_memory _ _ _ rfl state pointer watched atPointer
  intro entry member
  apply separate entry.1
  simp only [storeBE32ByteStores,List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide

theorem storeBE32_call_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer value watched : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word value)]) (code : state.code = originalRuntimeCode)
    (separate : ∀ offset : Nat, offset < 4 → watched ≠ panByteAlignHOL (pointer + BitVec.ofNat 64 offset))
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "st_be32") arguments) = (none,post)) :
    post.memory watched = state.memory watched := by
  have installed : state.code.lookup (ofString "st_be32") =
      some ([(ofString "p",.one),(ofString "v",.one)],sourceFunctionBody Guest.guestFn_st_be32,.one) := by
    rw [code]; exact originalRuntimeCode_storeBE32_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "st_be32") (ofString "p") (ofString "v")
    (sourceFunctionBody Guest.guestFn_st_be32) pointer value (by decide) installed
  obtain ⟨returned,output,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "st_be32")
    .one arguments _ _ _ args lookup run
  have frame := storeBE32_body_memory
    (callEntryStateHOLFinite state ((HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update
      (ofString "v",.val (.word value)))) pointer watched
    (by simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) separate
  rw [bodyRun] at frame
  rw [postEq]
  exact frame

#print axioms source_storeBE32_byte_plan
#print axioms storeBE32_body_memory
#print axioms storeBE32_call_normal_memory
end InitECandidate.Runtime
