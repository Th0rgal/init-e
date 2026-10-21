import ActualCandidateScratchEval
import InitECandidate.Runtime.PanTotalExpressionCost
import InitECandidate.Runtime.PanStatementWork

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The memory map after one candidate header word store. -/
noncomputable def candidateHeaderMemory {F : Type}
    (s : PanSemStateFiniteExact 64 F) (address value : BitVec 64) :
    RiscV.Word 64 → HolWordLab 64 :=
  fun current => if current = address then .word value else s.memory current

/-- One successful word store of the candidate header, with the explicit
updated memory map.  The destination is writable by hypothesis; the value is a
single word, so one address needs to be in the domain. -/
theorem candidate_header_store_word {F : Type} (fn : MlS)
    (s : PanSemStateFiniteExact 64 F) (destination source : ExpHOL 64)
    (address value : BitVec 64) (addressEvents valueEvents : List WorkEvent)
    (dst : CostedExpressionRun s destination (some (.val (.word address))) addressEvents)
    (src : CostedExpressionRun s source (some (.val (.word value))) valueEvents)
    (domain : s.memaddrs address) :
    StatementRun fn s (.store destination source) none
      { s with memory := candidateHeaderMemory s address value }
      (.statement :: (addressEvents ++ valueEvents ++
        [.memory (flattenHOL (.val (.word value))).length,
          .cost (storeOverhead (flattenHOL (.val (.word value))).length)])) := by
  refine StatementRun.storeValue (fn := fn) dst src ?_
  simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, candidateHeaderMemory]
  rw [if_pos domain]
  rfl

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidate_header_store_word
