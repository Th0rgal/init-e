import InitECandidate.Runtime.HeaderWordFieldStepContentReach
/-!
Per-word frame outside the actual written destination.

The actual header word parse only touches memory at or below the workspace ceiling
and the following store changes exactly the eight bytes it writes, so a header word
field step leaves every word at or above the ceiling unchanged except the one
destination.  This is the additive strengthening of the store and step content
reaches used to carry an already stored field (for instance the state root word at
offset 32) through the remaining decoder steps.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000


/-- The actual header word store keeps every other word, not only the words below
the record: the written word is the sole memory destination it changes. -/
theorem header_word_store_content_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength record value : BitVec 64) (offset : Nat) (name : MlS)
    (continuation : ProgHOL 64) (code : s.code = originalRuntimeCode)
    (atRecord : s.locals.lookup (ofString "h") = some (.val (.word record)))
    (atValue : s.locals.lookup name = some (.val (.word value)))
    (offsetBound : offset < 248) (recordFits : record.toNat + 248 < 2^64)
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (before : array.toNat + count.toNat * 16 ≤ record.toNat) :
    Reaches s (.seq (headerWordStore name offset) continuation)
      (fun post => post.memaddrs (record + BitVec.ofNat 64 offset) ∧
        post.memory (record + BitVec.ofNat 64 offset) = .word value ∧
        RlpSliceInputPrefix post array input inputLength count.toNat ∧
        post.locals = s.locals ∧ post.globals = s.globals ∧ post.memaddrs = s.memaddrs ∧ post.code = s.code ∧
        (∀ address : BitVec 64, address ≠ record + BitVec.ofNat 64 offset →
          post.memory address = s.memory address))
      0 continuation := by
  apply runBounded_seq_reaches s (headerWordStore name offset) continuation _ 0
    (RunBounded.ofProg (ProgBounded.straight _ rfl) code (by omega))
  · intro v
    exact evaluate_noDirectReturn (headerWordStore name offset) rfl s v
  · intro post normal
    have control := evaluate_store_control_frame s
      (.op .add [.var .local (ofString "h"),.const (BitVec.ofNat 64 offset)]) (.var .local name)
    have metadata := evaluateHOLFiniteState_metadata s (headerWordStore name offset)
    change evaluateHOLFiniteState s (.store _ _) = _ at normal
    rw [normal] at control
    change evaluateHOLFiniteState s (headerWordStore name offset) = _ at normal
    rw [normal] at metadata
    have globals : (evaluateHOLFiniteState s (headerWordStore name offset)).2.globals = s.globals := by
      unfold headerWordStore
      rw [evaluateHOLFiniteState_store]
      repeat' first | split | rfl
    rw [normal] at globals
    have memory : ∀ address : BitVec 64, address ≠ record + BitVec.ofNat 64 offset →
        post.memory address = s.memory address := by
      intro address different
      have frame := evaluate_wordStore_memory_frame s
        (.op .add [.var .local (ofString "h"),.const (BitVec.ofNat 64 offset)]) (.var .local name) (record + BitVec.ofNat 64 offset) address
        (by simp [evalHOLExact,evalListHOLExact,atRecord,wordOpHOL,wordOp,valueIsWord,valueWord])
        (by intro parsed ev; exact ⟨value,by simpa [evalHOLExact,atValue] using ev.symm⟩)
        (by intro same; exact different same)
      change (evaluateHOLFiniteState s (headerWordStore name offset)).2.memory address = s.memory address at frame
      rw [normal] at frame
      exact frame
    have stored := header_word_store_content s post record value offset name atRecord atValue normal
    have destAbove : ∀ address : BitVec 64, address.toNat < record.toNat →
        address ≠ record + BitVec.ofNat 64 offset := by
      intro address below same
      have offsetNat : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
      have destNat : (record + BitVec.ofNat 64 offset).toNat = record.toNat + offset := by
        rw [BitVec.toNat_add_of_lt (by rw [offsetNat]; omega),offsetNat]
      rw [same,destNat] at below
      omega
    exact ⟨stored.1,stored.2,
      table.after_memory_below s post array count input inputLength record before metadata.2.1
        (fun address below => memory address (destAbove address below)),
      control.2.1,globals,metadata.2.1,metadata.1,memory⟩

#print axioms header_word_store_content_frame

/-- The actual header word field step keeps every word at or above the ceiling
except the destination it writes, so words already stored in the header record at
other offsets survive any later step. -/
theorem header_word_field_step_content_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record : BitVec 64) (ceiling inputLimit : Nat)
    (index : BitVec 64) (offset : Nat) (continuation : ProgHOL 64)
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
    (budget : headerRlpFieldCost inputLimit + 35 ≤ s.clock) :
    Reaches s (headerWordFieldStep index offset continuation)
      (fun ready => ∃ word : BitVec 64,
        ready.memaddrs (record + BitVec.ofNat 64 offset) ∧
        ready.memory (record + BitVec.ofNat 64 offset) = .word word ∧
        ready.locals = s.locals.update (ofString "w",.val (.word word)) ∧
        RlpSliceInputPrefix ready array input inputLength count.toNat ∧
        ready.memaddrs = s.memaddrs ∧ ready.code = s.code ∧
        (∀ global : MlS, ready.globals.lookup global = s.globals.lookup global) ∧
        (∀ address : BitVec 64, ceiling ≤ address.toNat → address ≠ record + BitVec.ofNat 64 offset →
          ready.memory address = s.memory address))
      (headerRlpFieldCost inputLimit + 35) continuation := by
  obtain ⟨pointer,length,entry⟩ := table index inside
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "arr"),.const index] =
      some (headerNumericFieldValues .word array index 0) := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,atArray,headerNumericFieldValues]
  unfold headerWordFieldStep
  apply reaches_trans s _ (.seq (headerWordStore (ofString "w") offset) continuation) continuation _ _
    (headerRlpFieldCost inputLimit + 35) 0
    (header_numeric_field_assignment_reaches s .word array index 0 pointer length input inputLength scratch frame ceiling inputLimit
      (ofString "w") [.var .local (ofString "arr"),.const index]
      (.seq (headerWordStore (ofString "w") offset) continuation) args entry inputBound limitBound scratchGlobal frameGlobal code
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
  have atValue : parsed.locals.lookup (ofString "w") = some (.val (.word word)) := by
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have store := header_word_store_content_frame parsed array count input inputLength record word offset (ofString "w") continuation
    (installed.trans code) atRecordParsed atValue offsetBound recordFits tableParsed before
  apply reaches_mono parsed _ continuation _ _ 0 0 (le_refl _) ?_ store
  intro ready kept
  obtain ⟨storedDomain,storedWord,tableReady,localsReady,globalsReady,domainReady,codeReady,memoryReady⟩ := kept
  refine ⟨word,storedDomain,storedWord,localsReady.trans locals,tableReady,domainReady.trans domain,codeReady.trans installed,?_,?_⟩
  · intro global
    rw [globalsReady]
    exact globals global
  · intro address lo different
    exact (memoryReady address different).trans (memory address lo)

#print axioms header_word_field_step_content_frame

end InitECandidate.Runtime
