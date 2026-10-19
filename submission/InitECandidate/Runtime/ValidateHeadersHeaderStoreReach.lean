import InitECandidate.Runtime.ValidateHeadersFirstTailSource
import InitECandidate.Runtime.DecodeHeaderFlagStoreReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual decoded-header pointer store keeps every
older witness-table word, or terminates without consuming source clock. -/
theorem validate_headers_header_store_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength hs index header : BitVec 64) (continuation : ProgHOL 64) (code : s.code = originalRuntimeCode)
    (atHs : s.locals.lookup (ofString "hs") = some (.val (.word hs)))
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (atHeader : s.locals.lookup (ofString "h") = some (.val (.word header)))
    (destinationFits : hs.toNat + index.toNat * 8 < 2^64)
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (before : array.toNat + count.toNat * 16 ≤ hs.toNat) :
    Reaches s (.seq (validateHeadersHeaderStore) continuation)
      (fun post => RlpSliceInputPrefix post array input inputLength count.toNat ∧
        post.locals = s.locals ∧ post.globals = s.globals ∧ post.memaddrs = s.memaddrs ∧ post.code = s.code ∧
        (∀ address : BitVec 64, address.toNat < hs.toNat → post.memory address = s.memory address))
      0 continuation := by
  apply runBounded_seq_reaches s (validateHeadersHeaderStore) continuation _ 0
    (RunBounded.ofProg (ProgBounded.straight _ rfl) code (by omega))
  · intro v
    exact evaluate_noDirectReturn (validateHeadersHeaderStore) rfl s v
  · intro post normal
    have control := evaluate_store_control_frame s
      (.op .add [.var .local (ofString "hs"),.panop .mul [.var .local (ofString "i"),.const 8]]) (.var .local (ofString "h"))
    have metadata := evaluateHOLFiniteState_metadata s (validateHeadersHeaderStore)
    change evaluateHOLFiniteState s (.store _ _) = _ at normal
    rw [normal] at control
    change evaluateHOLFiniteState s (validateHeadersHeaderStore) = _ at normal
    rw [normal] at metadata
    have globals : (evaluateHOLFiniteState s (validateHeadersHeaderStore)).2.globals = s.globals := by
      unfold validateHeadersHeaderStore
      rw [evaluateHOLFiniteState_store]
      repeat' first | split | rfl
    rw [normal] at globals
    have memory : ∀ address : BitVec 64, address.toNat < hs.toNat → post.memory address = s.memory address := by
      intro address below
      have frame := evaluate_wordStore_memory_frame s
        (.op .add [.var .local (ofString "hs"),.panop .mul [.var .local (ofString "i"),.const 8]]) (.var .local (ofString "h")) (hs + index * 8) address
        (by simp [evalHOLExact,evalListHOLExact,atHs,atIndex,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord])
        (by intro parsed ev; exact ⟨header,by simpa [evalHOLExact,atHeader] using ev.symm⟩)
        (by
          have productNat : (index * 8).toNat = index.toNat * 8 := by
            rw [BitVec.toNat_mul_of_lt (by change index.toNat * 8 < 2^64; omega)]
            rfl
          have destinationNat : (hs + index * 8).toNat = hs.toNat + index.toNat * 8 := by
            rw [BitVec.toNat_add_of_lt (by rw [productNat]; exact destinationFits),productNat]
          intro same
          rw [same,destinationNat] at below
          omega)
      change (evaluateHOLFiniteState s (validateHeadersHeaderStore)).2.memory address = s.memory address at frame
      rw [normal] at frame
      exact frame
    exact ⟨table.after_memory_below s post array count input inputLength hs before metadata.2.1 memory,
      control.2.1,globals,metadata.2.1,metadata.1,memory⟩

#print axioms validate_headers_header_store_reaches
end InitECandidate.Runtime
