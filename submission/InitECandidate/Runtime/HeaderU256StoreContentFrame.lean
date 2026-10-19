import InitECandidate.Runtime.HeaderU256StoreReach
/-!
The actual four-limb store keeps every watched word at or above the ceiling.

`header_u256_store_reaches` only promises that words below the record are kept.
The returned record word at offset 32 has to survive the later numeric phases, so
this module records the same actual store with a ceiling-based frame instead: every
word at or above the workspace ceiling other than the four destinations the store
writes is left exactly as it was.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A real four-word store within the allocated header record keeps every word at
or above the ceiling except its own four destinations, or terminates without
consuming source clock. -/
theorem header_u256_store_content_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength record first second third fourth : BitVec 64) (offset : Nat) (name : MlS)
    (ceiling : Nat) (continuation : ProgHOL 64) (code : s.code = originalRuntimeCode)
    (atRecord : s.locals.lookup (ofString "h") = some (.val (.word record)))
    (atValue : s.locals.lookup name = some (.rStruct [.val (.word first),.val (.word second),.val (.word third),.val (.word fourth)]))
    (offsetBound : offset + 32 ≤ 248) (recordFits : record.toNat + 248 < 2^64)
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (before : array.toNat + count.toNat * 16 ≤ record.toNat) :
    Reaches s (.seq (headerWordStore name offset) continuation)
      (fun post => RlpSliceInputPrefix post array input inputLength count.toNat ∧
        post.locals = s.locals ∧ post.globals = s.globals ∧ post.memaddrs = s.memaddrs ∧ post.code = s.code ∧
        (∀ address : BitVec 64, ceiling ≤ address.toNat →
          address ≠ record + BitVec.ofNat 64 offset →
          address ≠ record + BitVec.ofNat 64 offset + 8#64 →
          address ≠ record + BitVec.ofNat 64 offset + 16#64 →
          address ≠ record + BitVec.ofNat 64 offset + 24#64 →
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
    have memory : ∀ address : BitVec 64, ceiling ≤ address.toNat →
        address ≠ record + BitVec.ofNat 64 offset →
        address ≠ record + BitVec.ofNat 64 offset + 8#64 →
        address ≠ record + BitVec.ofNat 64 offset + 16#64 →
        address ≠ record + BitVec.ofNat 64 offset + 24#64 →
        post.memory address = s.memory address := by
      intro address above apart0 apart8 apart16 apart24
      have frame := evaluate_fourWordStore_memory_frame s
        (.op .add [.var .local (ofString "h"),.const (BitVec.ofNat 64 offset)]) (.var .local name)
        (record + BitVec.ofNat 64 offset) first second third fourth address
        (by simp [evalHOLExact,evalListHOLExact,atRecord,wordOpHOL,wordOp,valueIsWord,valueWord])
        (by simpa [evalHOLExact] using atValue)
        apart0 apart8 apart16 apart24
      change (evaluateHOLFiniteState s (headerWordStore name offset)).2.memory address = s.memory address at frame
      rw [normal] at frame
      exact frame
    have below : ∀ address : BitVec 64, address.toNat < record.toNat → post.memory address = s.memory address := by
      intro address low
      have separate (k : BitVec 64) (small : k.toNat ≤ 24) : address ≠ (record + BitVec.ofNat 64 offset) + k := by
        have offsetNat : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
        have destinationNat : (record + BitVec.ofNat 64 offset).toNat = record.toNat + offset := by
          rw [BitVec.toNat_add_of_lt (by rw [offsetNat]; omega),offsetNat]
        have shiftedNat : ((record + BitVec.ofNat 64 offset) + k).toNat = record.toNat + offset + k.toNat := by
          rw [BitVec.toNat_add_of_lt (by rw [destinationNat]; omega),destinationNat]
        intro same
        rw [same,shiftedNat] at low
        omega
      have frame := evaluate_fourWordStore_memory_frame s
        (.op .add [.var .local (ofString "h"),.const (BitVec.ofNat 64 offset)]) (.var .local name)
        (record + BitVec.ofNat 64 offset) first second third fourth address
        (by simp [evalHOLExact,evalListHOLExact,atRecord,wordOpHOL,wordOp,valueIsWord,valueWord])
        (by simpa [evalHOLExact] using atValue)
        (by simpa using separate (0#64) (by decide))
        (separate (8#64) (by decide)) (separate (16#64) (by decide)) (separate (24#64) (by decide))
      change (evaluateHOLFiniteState s (headerWordStore name offset)).2.memory address = s.memory address at frame
      rw [normal] at frame
      exact frame
    exact ⟨table.after_memory_below s post array count input inputLength record before metadata.2.1 below,
      control.2.1,globals,metadata.2.1,metadata.1,memory⟩

#print axioms header_u256_store_content_frame
end InitECandidate.Runtime
