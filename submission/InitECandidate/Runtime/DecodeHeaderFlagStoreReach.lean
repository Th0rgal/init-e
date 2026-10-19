import InitECandidate.Runtime.DecodeHeaderCountGuard
import InitECandidate.Runtime.WordStoreMemoryFrame
import InitECandidate.Runtime.RlpSliceInputPrefixBelow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def decodeHeaderFlagStore : ProgHOL 64 := .store
  (.op .add [.var .local (ofString "h"),.const 0]) (.var .local (ofString "is_current"))

theorem source_decode_header_flag_store : decodeHeaderAt 8 = .seq decodeHeaderFlagStore (decodeHeaderAt 9) := rfl

/-- The original first header-record store retains the old slice table below
its newly allocated record. A failing store terminates within the same zero cost. -/
theorem decode_header_flag_store_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength record flag : BitVec 64) (code : s.code = originalRuntimeCode)
    (atRecord : s.locals.lookup (ofString "h") = some (.val (.word record)))
    (atFlag : s.locals.lookup (ofString "is_current") = some (.val (.word flag)))
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (before : array.toNat + count.toNat * 16 ≤ record.toNat) :
    Reaches s (decodeHeaderAt 8)
      (fun post => RlpSliceInputPrefix post array input inputLength count.toNat ∧
        post.locals = s.locals ∧ post.globals = s.globals ∧ post.memaddrs = s.memaddrs ∧ post.code = s.code ∧
        (∀ address : BitVec 64, address.toNat < record.toNat → post.memory address = s.memory address))
      0 (decodeHeaderAt 9) := by
  rw [source_decode_header_flag_store]
  apply runBounded_seq_reaches s decodeHeaderFlagStore (decodeHeaderAt 9) _ 0
    (RunBounded.ofProg (ProgBounded.straight _ rfl) code (by omega))
  · intro v
    exact evaluate_noDirectReturn decodeHeaderFlagStore rfl s v
  · intro post normal
    have control := evaluate_store_control_frame s
      (.op .add [.var .local (ofString "h"),.const 0]) (.var .local (ofString "is_current"))
    have metadata := evaluateHOLFiniteState_metadata s decodeHeaderFlagStore
    change evaluateHOLFiniteState s (.store _ _) = _ at normal
    rw [normal] at control
    change evaluateHOLFiniteState s decodeHeaderFlagStore = _ at normal
    rw [normal] at metadata
    have globals : (evaluateHOLFiniteState s decodeHeaderFlagStore).2.globals = s.globals := by
      unfold decodeHeaderFlagStore
      rw [evaluateHOLFiniteState_store]
      repeat' first | split | rfl
    rw [normal] at globals
    have memory : ∀ address : BitVec 64, address.toNat < record.toNat → post.memory address = s.memory address := by
      intro address below
      have frame := evaluate_wordStore_memory_frame s
        (.op .add [.var .local (ofString "h"),.const 0]) (.var .local (ofString "is_current")) record address
        (by simp [evalHOLExact,evalListHOLExact,atRecord,wordOpHOL,wordOp,valueIsWord,valueWord])
        (by intro value ev; exact ⟨flag,by simpa [evalHOLExact,atFlag] using ev.symm⟩)
        (by intro same; rw [same] at below; omega)
      change (evaluateHOLFiniteState s decodeHeaderFlagStore).2.memory address = s.memory address at frame
      rw [normal] at frame
      exact frame
    exact ⟨table.after_memory_below s post array count input inputLength record before metadata.2.1 memory,
      control.2.1,globals,metadata.2.1,metadata.1,memory⟩

#print axioms source_decode_header_flag_store
#print axioms decode_header_flag_store_reaches
end InitECandidate.Runtime
