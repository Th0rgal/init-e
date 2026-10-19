import InitECandidate.Runtime.HeaderWordStoreReach
import InitECandidate.Runtime.FourWordStoreMemoryFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A real four-word store within the allocated header record keeps every
older slice-table word, or terminates without consuming source clock. -/
theorem header_u256_store_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength record first second third fourth : BitVec 64) (offset : Nat) (name : MlS)
    (continuation : ProgHOL 64) (code : s.code = originalRuntimeCode)
    (atRecord : s.locals.lookup (ofString "h") = some (.val (.word record)))
    (atValue : s.locals.lookup name = some (.rStruct [.val (.word first),.val (.word second),.val (.word third),.val (.word fourth)]))
    (offsetBound : offset + 32 ≤ 248) (recordFits : record.toNat + 248 < 2^64)
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (before : array.toNat + count.toNat * 16 ≤ record.toNat) :
    Reaches s (.seq (headerWordStore name offset) continuation)
      (fun post => RlpSliceInputPrefix post array input inputLength count.toNat ∧
        post.locals = s.locals ∧ post.globals = s.globals ∧ post.memaddrs = s.memaddrs ∧ post.code = s.code ∧
        (∀ address : BitVec 64, address.toNat < record.toNat → post.memory address = s.memory address))
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
    have memory : ∀ address : BitVec 64, address.toNat < record.toNat → post.memory address = s.memory address := by
      intro address below
      have separate (k : BitVec 64) (small : k.toNat ≤ 24) : address ≠ (record + BitVec.ofNat 64 offset) + k := by
        have offsetNat : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
        have destinationNat : (record + BitVec.ofNat 64 offset).toNat = record.toNat + offset := by
          rw [BitVec.toNat_add_of_lt (by rw [offsetNat]; omega),offsetNat]
        have shiftedNat : ((record + BitVec.ofNat 64 offset) + k).toNat = record.toNat + offset + k.toNat := by
          rw [BitVec.toNat_add_of_lt (by rw [destinationNat]; omega),destinationNat]
        intro same
        rw [same,shiftedNat] at below
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
    exact ⟨table.after_memory_below s post array count input inputLength record before metadata.2.1 memory,
      control.2.1,globals,metadata.2.1,metadata.1,memory⟩

#print axioms header_u256_store_reaches
end InitECandidate.Runtime
