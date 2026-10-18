import InitECandidate.Runtime.SecpInitSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxHeartbeats 1000000

/-- The eight words written by one accelerator block initialization: c = 0
at base+64 and the modulus at base+96. -/
def secpBlockCells (m0 m1 m2 m3 : BitVec 64) : List (BitVec 64 × BitVec 64) :=
  [(64,0),(72,0),(80,0),(88,0),(96,m0),(104,m1),(112,m2),(120,m3)]

theorem evaluate_secpAccelInitBlock_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (base m0 m1 m2 m3 : BitVec 64)
    (atBase : state.locals.lookup (ofString "base") = some (.val (.word base)))
    (atModulus : state.locals.lookup (ofString "modulus") =
      some (.rStruct [.val (.word m0),.val (.word m1),.val (.word m2),.val (.word m3)]))
    (domain : ∀ cell ∈ secpBlockCells m0 m1 m2 m3, state.memaddrs (base + cell.1)) :
    evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_secp_accel_init_block) =
      (some (.returned (.val (.word 0))),
        emptyLocalsHOLFinite {state with memory := memWrites state.memory base (secpBlockCells m0 m1 m2 m3)}) := by
  have d : ∀ k v : BitVec 64, (k, v) ∈ secpBlockCells m0 m1 m2 m3 → state.memaddrs (base + k) := by
    intro k v member; exact domain _ member
  have d64 := d 64 0 (by simp [secpBlockCells])
  have d72 := d 72 0 (by simp [secpBlockCells])
  have d80 := d 80 0 (by simp [secpBlockCells])
  have d88 := d 88 0 (by simp [secpBlockCells])
  have d96 := d 96 m0 (by simp [secpBlockCells])
  have d104 := d 104 m1 (by simp [secpBlockCells])
  have d112 := d 112 m2 (by simp [secpBlockCells])
  have d120 := d 120 m3 (by simp [secpBlockCells])
  have assoc : ∀ a b : BitVec 64, base + a + b = base + (a + b) := fun a b => BitVec.add_assoc _ _ _
  have first := evaluate_store_four_words state (base + 64) 0 0 0 0
    (.op .add [.var .local (ofString "base"),.const 64]) (.rstruct [.const 0,.const 0,.const 0,.const 0])
    (by simp [evalHOLExact,evalListHOLExact,atBase,wordOpHOL,wordOp,valueIsWord,valueWord])
    (by simp [evalHOLExact,evalListHOLExact])
    d64 (by rw [assoc]; exact d72) (by rw [assoc]; exact d80) (by rw [assoc]; exact d88)
  let mid := journalRecordPost32 state (base + 64) 0 0 0 0
  have midBase : mid.locals.lookup (ofString "base") = some (.val (.word base)) := atBase
  have midModulus : mid.locals.lookup (ofString "modulus") =
      some (.rStruct [.val (.word m0),.val (.word m1),.val (.word m2),.val (.word m3)]) := atModulus
  have second := evaluate_store_four_words mid (base + 96) m0 m1 m2 m3
    (.op .add [.var .local (ofString "base"),.const 96]) (.var .local (ofString "modulus"))
    (by simp [evalHOLExact,evalListHOLExact,midBase,wordOpHOL,wordOp,valueIsWord,valueWord])
    (by simp [evalHOLExact,midModulus])
    d96 (by rw [assoc]; exact d104) (by rw [assoc]; exact d112) (by rw [assoc]; exact d120)
  rw [source_secpAccelInitBlock_body,evaluateHOLFiniteState_seq_line780,first]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780,second]
  dsimp only
  simp only [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  have post : journalRecordPost32 mid (base + 96) m0 m1 m2 m3 =
      {state with memory := memWrites state.memory base (secpBlockCells m0 m1 m2 m3)} := by
    simp only [journalRecordPost32,sourceWriteWord,mid]
    congr 1
    funext a
    simp only [memWrites,wmem,secpBlockCells,BitVec.add_assoc,BitVec.reduceAdd]
    rfl
  rw [if_pos (by simp [sizeOfShapeWithContextHOL]),post]

#print axioms evaluate_secpAccelInitBlock_body
end InitECandidate.Runtime
