import InitECandidate.Runtime.DecodeWitnessSelectedReturnedMemory
import InitECandidate.Runtime.DecodeWitnessReturnedMemoryPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Complete original root-decoder returned heap contract, including empty roots
and actual optional final hash allocation. No successful room is assumed. -/
theorem decode_witness_to_mpt_returned_memory {F : Type} (layout : WitnessTraversalLayout)
 (s post : PanSemStateFiniteExact 64 F) (scratch heap originalPointer originalLength root emptyRoot : BitVec 64)
 (value : ValueHOL 64)
 (valid : WitnessTraversalEntryPrecondition layout s scratch heap originalPointer originalLength)
 (atRoot : s.locals.lookup (ofString "root_hash")=some (.val (.word root)))
 (atEmpty : s.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
 (budget : decodeWitnessToMptSourceCeiling≤s.clock)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_decode_witness_to_mpt)=(some (.returned value),post)) :
 ∀watched : BitVec 64,layout.databaseCeiling≤watched.toNat→watched.toNat<layout.dbHeap.toNat→post.memory watched=s.memory watched := by
 change evaluateHOLFiniteState s (decodeWitnessAt 0)=(some (.returned value),post) at run
 have beforeNode := decode_witness_returned_memory_prefix s layout.table layout.dbHeap layout.total root emptyRoot
  layout.dbArray layout.input layout.inputLength valid.built valid.entries valid.slices valid.atDb atRoot atEmpty valid.code
  (by unfold decodeWitnessToMptSourceCeiling at budget;omega)
 rcases beforeNode with ⟨returned,bounded,globals,memory⟩ | reaches
 · rw [run] at memory
   intro watched lo hi
   rw [memory]
 · rcases reaches with ⟨next,facts,spent,remaining,agreement⟩ | abort
   · obtain ⟨found,pointer,length,nonzero,atResult,atTable,atNextRoot,memory,globals,installed,domain,endian,lo,hi,nowrap,small⟩ := facts
     have entered := valid.after_read layout s next scratch heap originalPointer originalLength pointer length
      memory globals installed domain endian atTable lo hi nowrap small
     rw [run] at agreement
     let output := (evaluateHOLFiniteState next (decodeWitnessAt 4)).2
     have inner : evaluateHOLFiniteState next (decodeWitnessAt 4)=(some (.returned value),output) :=
      Prod.ext agreement.1.symm rfl
     have frame := decode_witness_selected_returned_memory layout next output scratch heap pointer length found root value entered
      atResult atNextRoot (by unfold decodeWitnessToMptSourceCeiling at budget;omega) inner
     intro watched lower upper
     rw [agreement.2.2.1,frame watched lower upper,memory]
   · obtain ⟨result,equal,notReturned,_,_,_⟩ := abort
     rw [run] at equal
     cases Option.some.inj equal
     exact False.elim (notReturned value rfl)
#print axioms decode_witness_to_mpt_returned_memory
end InitECandidate.Runtime
