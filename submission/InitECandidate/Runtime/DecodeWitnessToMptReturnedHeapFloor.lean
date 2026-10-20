import InitECandidate.Runtime.DecodeWitnessSelectedReturnedHeapFloor
import InitECandidate.Runtime.DecodeWitnessReturnedContextPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Complete original root-decoder returned heap contract, including empty roots
and actual optional final hash allocation. No successful room is assumed. -/
theorem decode_witness_to_mpt_returned_heap_floor {F : Type} (layout : WitnessTraversalLayout)
 (s post : PanSemStateFiniteExact 64 F) (scratch heap originalPointer originalLength root emptyRoot : BitVec 64)
 (value : ValueHOL 64)
 (valid : WitnessTraversalEntryPrecondition layout s scratch heap originalPointer originalLength)
 (atRoot : s.locals.lookup (ofString "root_hash")=some (.val (.word root)))
 (atEmpty : s.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
 (budget : decodeWitnessToMptSourceCeiling≤s.clock)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_decode_witness_to_mpt)=(some (.returned value),post)) :
 (∃nextHeap : BitVec 64,post.globals.lookup (ofString "heap_ptr")=some (.val (.word nextHeap)) ∧nextHeap.toNat%8=0 ∧nextHeap.toNat≤33806089496 ∧layout.persistentFloor≤nextHeap.toNat) := by
 change evaluateHOLFiniteState s (decodeWitnessAt 0)=(some (.returned value),post) at run
 have beforeNode := decode_witness_returned_context_prefix s layout.table layout.dbHeap layout.total root emptyRoot
  layout.dbArray layout.input layout.inputLength valid.built valid.entries valid.slices valid.atDb atRoot atEmpty valid.code
  (by unfold decodeWitnessToMptSourceCeiling at budget;omega)
 rcases beforeNode with ⟨returned,bounded,globals⟩ | reaches
 · rw [run] at globals
   exact ⟨heap,by rw [globals];exact valid.atHeap,valid.heapAligned,valid.heapBound,valid.floorBeforeHeap⟩
 · rcases reaches with ⟨next,facts,spent,remaining,agreement⟩ | abort
   · obtain ⟨found,pointer,length,nonzero,atResult,atTable,atNextRoot,memory,globals,installed,domain,endian,lo,hi,nowrap,small⟩ := facts
     have entered := valid.after_read layout s next scratch heap originalPointer originalLength pointer length
      memory globals installed domain endian atTable lo hi nowrap small
     rw [run] at agreement
     let output := (evaluateHOLFiniteState next (decodeWitnessAt 4)).2
     have inner : evaluateHOLFiniteState next (decodeWitnessAt 4)=(some (.returned value),output) :=
      Prod.ext agreement.1.symm rfl
     have ready := decode_witness_selected_returned_heap_floor layout next output scratch heap pointer length found value entered
      atResult (by unfold decodeWitnessToMptSourceCeiling at budget;omega) inner
     obtain ⟨p,h,al,cap,floor⟩ := ready
     exact ⟨p,by rw [agreement.2.2.2.1];exact h,al,cap,floor⟩
   · obtain ⟨result,equal,notReturned,_,_,_⟩ := abort
     rw [run] at equal
     cases Option.some.inj equal
     exact False.elim (notReturned value rfl)
#print axioms decode_witness_to_mpt_returned_heap_floor
end InitECandidate.Runtime
