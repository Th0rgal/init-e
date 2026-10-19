import InitECandidate.Runtime.DecodeHeaderFirstFieldStoreReach
import InitECandidate.Runtime.HeaderRlpFieldAssignmentReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

def headerBytesStep (index width : BitVec 64) (offset : Nat) (continuation : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (some (.local,ofString "f"),none)) (ofString "hdr_bytes_field")
    [.var .local (ofString "arr"),.const index,.const width])
    (.seq (headerWordStore (ofString "f") offset) continuation)

/-- An actual bytes-field assignment and record store consume a readable
entry and preserve the entire field table for the next parser call. -/
theorem header_bytes_step_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record : BitVec 64) (ceiling inputLimit : Nat)
    (index width : BitVec 64) (offset : Nat) (continuation : ProgHOL 64)
    (offsetBound : offset < 248)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atRecord : s.locals.lookup (ofString "h") = some (.val (.word record)))
    (before : array.toNat + count.toNat * 16 ≤ record.toNat)
    (recordFits : record.toNat + 248 < 2^64)
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (inside : index.toNat < count.toNat) (above : ceiling ≤ array.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : headerRlpFieldCost inputLimit + 1 ≤ s.clock) :
    Reaches s (headerBytesStep index width offset continuation)
      (fun ready => ∃ word : BitVec 64,
        ready.locals = s.locals.update (ofString "f",.val (.word word)) ∧
        RlpSliceInputPrefix ready array input inputLength count.toNat ∧
        ready.memaddrs = s.memaddrs ∧ ready.code = s.code ∧
        (∀ global : MlS, ready.globals.lookup global = s.globals.lookup global) ∧
        (∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < record.toNat →
          ready.memory address = s.memory address))
      (headerRlpFieldCost inputLimit + 1) continuation := by
  obtain ⟨pointer,length,entry⟩ := table index inside
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "arr"),.const index,.const width] =
      some (headerRlpFieldValues .bytes array index width) := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,atArray,headerRlpFieldValues]
  unfold headerBytesStep
  apply reaches_trans s _ (.seq (headerWordStore (ofString "f") offset) continuation) continuation _ _
    (headerRlpFieldCost inputLimit + 1) 0
    (header_rlp_field_assignment_reaches s .bytes array index width pointer length input inputLength scratch frame ceiling inputLimit
      (ofString "f") [.var .local (ofString "arr"),.const index,.const width]
      (.seq (headerWordStore (ofString "f") offset) continuation) args entry inputBound limitBound scratchGlobal frameGlobal code
      orderedFrame framePositive scratchBelow arena budget)
  intro parsed facts
  obtain ⟨value,locals,checked,domain,installed,globals,memory⟩ := facts
  have tableParsed : RlpSliceInputPrefix parsed array input inputLength count.toNat :=
    table.after_memory_from_ceiling s parsed array count input inputLength ceiling above fits domain memory
  obtain ⟨word,valueEq⟩ := value_word_of_shape_one value ((shapeEqHOL_eq_true _ _).mp checked)
  subst value
  have atRecordParsed : parsed.locals.lookup (ofString "h") = some (.val (.word record)) := by
    rw [locals]
    simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atRecord
  have atValue : parsed.locals.lookup (ofString "f") = some (.val (.word word)) := by
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have store := header_word_store_reaches parsed array count input inputLength record word offset (ofString "f") continuation
    (installed.trans code) atRecordParsed atValue offsetBound recordFits tableParsed before
  apply reaches_mono parsed _ continuation _ _ 0 0 (le_refl _) ?_ store
  intro ready kept
  obtain ⟨tableReady,localsReady,globalsReady,domainReady,codeReady,memoryReady⟩ := kept
  refine ⟨word,localsReady.trans locals,tableReady,domainReady.trans domain,codeReady.trans installed,?_,?_⟩
  · intro global
    rw [globalsReady]
    exact globals global
  · intro address lo hi
    exact (memoryReady address hi).trans (memory address lo)

#print axioms header_bytes_step_reaches
end InitECandidate.Runtime
