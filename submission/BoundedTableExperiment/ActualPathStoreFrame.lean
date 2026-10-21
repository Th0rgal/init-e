import InitECandidate.Runtime.ActualPayloadHeaderWatched
import InitECandidate.Runtime.PanStatementWork

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Actual PNK memory semantics: a one-word store leaves every different
watched cell unchanged. -/
theorem actual_one_word_store_frame (address watched : BitVec 64)
    (domain : BitVec 64 → Prop) [DecidablePred domain]
    (memory : BitVec 64 → HolWordLab 64) (value : HolWordLab 64)
    (different : watched ≠ address) (updated : BitVec 64 → HolWordLab 64)
    (run : panMemStoresHOL address [value] domain memory = some updated) :
    updated watched = memory watched := by
  apply InitECandidate.Runtime.panMemStoresHOL_frame address watched domain memory [value]
  · intro index bound
    have zero : index = 0 := by simpa using bound
    subst zero
    simpa using different
  · exact run

/-- The post-memory of an actual one-word `StatementRun.storeValue` is
unchanged at every watched cell other than the store address. -/
theorem actual_storeValue_frame {F : Type} {fn : Pancake.PanLang.MlS}
    {s : PanSemStateFiniteExact 64 F}
    {destination source : Pancake.PanLang.ExpHOL 64} {address watched : BitVec 64}
    {value : ValueHOL 64} {addressEvents valueEvents : List WorkEvent}
    (dst : CostedExpressionRun s destination
      (some (ValueHOL.val (HolWordLab.word address))) addressEvents)
    (src : CostedExpressionRun s source (some value) valueEvents)
    {memory : BitVec 64 → HolWordLab 64}
    (write : @panMemStoresHOL 64 _ address (flattenHOL value) s.memaddrs
      (Classical.decPred _) s.memory = some memory)
    (one : (flattenHOL value).length = 1)
    (different : watched ≠ address) :
    memory watched = s.memory watched := by
  have _ := dst
  have _ := src
  cases hwords : flattenHOL value with
  | nil => simp [hwords] at one
  | cons word rest =>
      cases rest with
      | nil =>
          letI : DecidablePred s.memaddrs := Classical.decPred _
          apply actual_one_word_store_frame address watched s.memaddrs s.memory word
          · exact different
          · simpa [hwords] using write
      | cons _ _ => simp [hwords] at one

end BoundedTableExperiment

#print axioms BoundedTableExperiment.actual_one_word_store_frame
#print axioms BoundedTableExperiment.actual_storeValue_frame
