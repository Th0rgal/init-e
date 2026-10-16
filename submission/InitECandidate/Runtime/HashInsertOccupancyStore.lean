import InitECandidate.Runtime.SourceByteReadback
import InitECandidate.Runtime.HashProbeSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def sourceFirstByteStore : ProgHOL 64 → Option (ProgHOL 64)
  | .storeByte destination value => some (.storeByte destination value)
  | .dec _ _ _ body => sourceFirstByteStore body
  | .decCall _ _ _ _ body => sourceFirstByteStore body
  | .seq first rest => (sourceFirstByteStore first).orElse (fun _ => sourceFirstByteStore rest)
  | _ => none

def hashInsertOccupancyStore : ProgHOL 64 :=
  .storeByte (.op .add [.var .local (ofString "used"),.var .local (ofString "i")]) (.const 1)

/-- Literal provenance of the occupancy write in the original insertion. -/
theorem source_htabInsert_occupancy_store :
    sourceFirstByteStore (sourceFunctionBody Guest.guestFn_htab_insert_raw) = some hashInsertOccupancyStore := by
  unfold sourceFunctionBody
  rw [declToHOL_eq]
  simp only [Guest.guestFn_htab_insert_raw,declToHOLStructural,funDeclToHOLStructural,
    progToHOLStructural,expToHOLStructural,expListToHOLStructural,shapeToHOLStructural,
    List.map_cons,List.map_nil,Option.map_none,sourceFirstByteStore,Option.orElse,hashInsertOccupancyStore]
  rfl

/-- The source insertion's exact occupancy store updates the actual count by
one, preserving all neighboring byte reads as established by the store law. -/
theorem evaluate_hashInsert_occupancy_store {F : Type} (state : PanSemStateFiniteExact 64 F)
    (capacity used slot cell : BitVec 64)
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word slot)))
    (inside : slot.toNat < capacity.toNat)
    (domain : state.memaddrs (panByteAlignHOL (used + slot)))
    (memory : state.memory (panByteAlignHOL (used + slot)) = .word cell)
    (empty : hashOccupancyRead state used slot = some 0) :
    ∃ post, evaluateHOLFiniteState state hashInsertOccupancyStore = (none,post) ∧
      hashOccupiedCount capacity (hashOccupancyRead post used) =
        hashOccupiedCount capacity (hashOccupancyRead state used) + 1 ∧ post.clock = state.clock := by
  refine ⟨sourceWriteByte state (used + slot) 1 cell,?_,?_,rfl⟩
  · apply evaluate_source_storeByte
    · simp [evalHOLExact,evalListHOLExact,usedLocal,indexLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
    · rfl
    · exact domain
    · exact memory
  · exact sourceWriteByte_occupancy_fill state capacity used slot cell inside domain memory empty

#print axioms source_htabInsert_occupancy_store
#print axioms evaluate_hashInsert_occupancy_store
end InitECandidate.Runtime
