import InitECandidate.Runtime.DecodeWitnessSelectedNodeBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxHeartbeats 1000000
/-- Fixed source-step ceiling for the complete original database-to-trie wrapper. -/
def decodeWitnessToMptSourceCeiling : Nat :=
 (129+(nodedbGetCost+3))+(witnessTraversalBodySourceCeiling+25)

/-- Complete actual decode_witness_to_mpt all-outcome bound from concrete original
input/database/workspace geometry. The selected slice entry is derived from the
real lookup result; no successful allocation or callee-bound callback is assumed. -/
theorem runBounded_decode_witness_to_mpt_uniform {F : Type} (layout : WitnessTraversalLayout)
 (s : PanSemStateFiniteExact 64 F) (scratch heap originalPointer originalLength root emptyRoot : BitVec 64)
 (valid : WitnessTraversalEntryPrecondition layout s scratch heap originalPointer originalLength)
 (atRoot : s.locals.lookup (ofString "root_hash")=some (.val (.word root)))
 (atEmpty : s.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
 (budget : decodeWitnessToMptSourceCeiling≤s.clock) :
 RunBounded s (sourceFunctionBody Guest.guestFn_decode_witness_to_mpt) decodeWitnessToMptSourceCeiling := by
 change RunBounded s (decodeWitnessAt 0) decodeWitnessToMptSourceCeiling
 have beforeNode :=  decode_witness_full_context_prefix s layout.table layout.dbHeap layout.total root emptyRoot
  layout.dbArray layout.input layout.inputLength valid.built valid.entries valid.slices valid.atDb atRoot atEmpty
  valid.code (by unfold decodeWitnessToMptSourceCeiling at budget;omega)
 rcases beforeNode with ⟨returned,bounded⟩ | reaches
 · exact bounded.weaken (by unfold decodeWitnessToMptSourceCeiling;omega)
 · apply RunBounded.ofReaches budget reaches
   intro next facts ticks
   obtain ⟨found,pointer,length,nonzero,atResult,atTable,atNextRoot,memory,globals,installed,domain,endian,lo,hi,nowrap,small⟩ := facts
   have entered := valid.after_read layout s next scratch heap originalPointer originalLength pointer length
    memory globals installed domain endian atTable lo hi nowrap small
   exact runBounded_decode_witness_selected_node layout next scratch heap pointer length found entered atResult ticks
#print axioms runBounded_decode_witness_to_mpt_uniform
end InitECandidate.Runtime
