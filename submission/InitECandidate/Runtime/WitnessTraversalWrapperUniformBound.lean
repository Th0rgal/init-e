import InitECandidate.Runtime.WitnessTraversalEntryContext
import InitECandidate.Runtime.DecodeWitnessWrapperBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual MptErr wrapper has a fixed finite cost, including release and
rethrow, from the concrete decoder entry precondition. -/
theorem runBounded_witness_mpt_uniform {F : Type} (layout : WitnessTraversalLayout)
    (s : PanSemStateFiniteExact 64 F) (scratch heap pointer length : BitVec 64)
    (valid : WitnessTraversalEntryPrecondition layout s scratch heap pointer length)
    (atPointer : s.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n")=some (.val (.word length)))
    (budget : witnessTraversalBodySourceCeiling+2≤s.clock) :
    RunBounded s (sourceFunctionBody Guest.guestFn__decode_witness_node_mpt) (witnessTraversalBodySourceCeiling+2) := by
  apply runBounded_decode_witness_mpt_wrapper s layout.table pointer length witnessTraversalBodySourceCeiling
    valid.atDb atPointer atLength valid.code budget
  simpa only [witnessTraversalArguments,decodeWitnessBodyCallee] using
    runBounded_witness_traversal_body_entry layout s scratch heap pointer length valid (by omega)

/-- The complete original witness decoder, including both exception handlers
and normal scratch cleanup, has a fixed finite source-step bound. The arena
precondition remains explicit until the canonical domain bridge is discharged. -/
theorem runBounded_witness_decoder_uniform {F : Type} (layout : WitnessTraversalLayout)
    (s : PanSemStateFiniteExact 64 F) (scratch heap pointer length : BitVec 64)
    (valid : WitnessTraversalEntryPrecondition layout s scratch heap pointer length)
    (atPointer : s.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n")=some (.val (.word length)))
    (budget : witnessTraversalBodySourceCeiling+6≤s.clock) :
    RunBounded s (sourceFunctionBody Guest.guestFn__decode_witness_node) (witnessTraversalBodySourceCeiling+6) := by
  let locals := decodeWitnessBodyCallee layout.table pointer length
  have entered := valid.with_locals_clock layout s scratch heap pointer length locals (s.clock-3)
    (by simp (config:={decide:=true}) [locals,decodeWitnessBodyCallee,HolFiniteMapExact.lookup_update,FUPDATE])
  change WitnessTraversalEntryPrecondition layout
    {callEntryStateHOLFinite s locals with clock:=s.clock-3} scratch heap pointer length at entered
  apply runBounded_decode_witness_wrapper s layout.table pointer length scratch witnessTraversalBodySourceCeiling
    valid.atDb atPointer atLength valid.atScratch valid.code budget
  exact runBounded_witness_traversal_body_uniform layout
    {callEntryStateHOLFinite s locals with clock:=s.clock-3} scratch heap pointer length entered
    (by simp (config:={decide:=true}) [locals,decodeWitnessBodyCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [locals,decodeWitnessBodyCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by change witnessTraversalBodySourceCeiling≤s.clock-3;omega)
#print axioms runBounded_witness_mpt_uniform
#print axioms runBounded_witness_decoder_uniform
end InitECandidate.Runtime
