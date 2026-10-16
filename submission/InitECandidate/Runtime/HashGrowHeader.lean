import InitECandidate.Runtime.HashGrowRehashSyntax
import InitECandidate.Runtime.HashInsertValueTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def hashGrowHeader (continuation : ProgHOL 64) : ProgHOL 64 :=
  (.seq (.store (hashLocalAddress (ofString "t") 16) (.var .local (ofString "ncap"))) (.seq (.store (hashLocalAddress (ofString "t") 32) (.var .local (ofString "nkeys"))) (.seq (.store (hashLocalAddress (ofString "t") 40) (.var .local (ofString "nvals"))) (.seq (.store (hashLocalAddress (ofString "t") 48) (.var .local (ofString "nused"))) (.seq (.store (hashLocalAddress (ofString "t") 56) (.var .local (ofString "norder"))) (.seq (.store (hashLocalAddress (ofString "t") 64) (.var .local (ofString "norder_pos"))) (.seq (.store (hashLocalAddress (ofString "t") 24) (.const 0)) continuation)))))))

theorem source_htabGrow_header_stores :
    sourceFirstCallContinuation (ofString "memzero") (sourceFunctionBody Guest.guestFn_htab_grow) =
      some (hashGrowHeader (.dec (ofString "k") .one (.const 0) (.seq hashGrowRehashLoop (.return (.const 0))))) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

noncomputable def htabGrowHeaderPost {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table capacity keys values used order orderPos : BitVec 64) :=
  (sourceWriteWord (sourceWriteWord (sourceWriteWord (sourceWriteWord (sourceWriteWord (sourceWriteWord (sourceWriteWord state (table + 16) capacity) (table + 32) keys) (table + 40) values) (table + 48) used) (table + 56) order) (table + 64) orderPos) (table + 24) 0)

/-- Execute the seven literal original growth header stores at zero clocks. -/
theorem evaluate_htabGrow_header {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table capacity keys values used order orderPos : BitVec 64) (continuation : ProgHOL 64)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (ncapLocal : state.locals.lookup (ofString "ncap") = some (.val (.word capacity)))
    (nkeysLocal : state.locals.lookup (ofString "nkeys") = some (.val (.word keys)))
    (nvalsLocal : state.locals.lookup (ofString "nvals") = some (.val (.word values)))
    (nusedLocal : state.locals.lookup (ofString "nused") = some (.val (.word used)))
    (norderLocal : state.locals.lookup (ofString "norder") = some (.val (.word order)))
    (norder_posLocal : state.locals.lookup (ofString "norder_pos") = some (.val (.word orderPos)))
    (domain16 : state.memaddrs (table + 16))
    (domain32 : state.memaddrs (table + 32))
    (domain40 : state.memaddrs (table + 40))
    (domain48 : state.memaddrs (table + 48))
    (domain56 : state.memaddrs (table + 56))
    (domain64 : state.memaddrs (table + 64))
    (domain24 : state.memaddrs (table + 24))
    : evaluateHOLFiniteState state (hashGrowHeader continuation) =
      evaluateHOLFiniteState (htabGrowHeaderPost state table capacity keys values used order orderPos) continuation := by
  let s1 := sourceWriteWord state (table + 16) capacity
  have run1 := evaluate_store_word state (table + 16) capacity _ (.var .local (ofString "ncap"))
    (eval_hashLocalAddress state (ofString "t") table 16 tableLocal) ncapLocal domain16
  let s2 := sourceWriteWord s1 (table + 32) keys
  have run2 := evaluate_store_word s1 (table + 32) keys _ (.var .local (ofString "nkeys"))
    (eval_hashLocalAddress s1 (ofString "t") table 32 tableLocal) nkeysLocal domain32
  let s3 := sourceWriteWord s2 (table + 40) values
  have run3 := evaluate_store_word s2 (table + 40) values _ (.var .local (ofString "nvals"))
    (eval_hashLocalAddress s2 (ofString "t") table 40 tableLocal) nvalsLocal domain40
  let s4 := sourceWriteWord s3 (table + 48) used
  have run4 := evaluate_store_word s3 (table + 48) used _ (.var .local (ofString "nused"))
    (eval_hashLocalAddress s3 (ofString "t") table 48 tableLocal) nusedLocal domain48
  let s5 := sourceWriteWord s4 (table + 56) order
  have run5 := evaluate_store_word s4 (table + 56) order _ (.var .local (ofString "norder"))
    (eval_hashLocalAddress s4 (ofString "t") table 56 tableLocal) norderLocal domain56
  let s6 := sourceWriteWord s5 (table + 64) orderPos
  have run6 := evaluate_store_word s5 (table + 64) orderPos _ (.var .local (ofString "norder_pos"))
    (eval_hashLocalAddress s5 (ofString "t") table 64 tableLocal) norder_posLocal domain64
  let s7 := sourceWriteWord s6 (table + 24) 0
  have run7 := evaluate_store_word s6 (table + 24) 0 _ (.const 0)
    (eval_hashLocalAddress s6 (ofString "t") table 24 tableLocal) (by rfl) domain24
  unfold hashGrowHeader
  rw [evaluateHOLFiniteState_seq_line780,run1]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780,run2]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780,run3]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780,run4]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780,run5]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780,run6]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780,run7]
  dsimp only
  rfl

/-- Readback of every changed header and retention of key width and stride. -/
theorem htabGrowHeaderPost_fields {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table capacity keys values used order orderPos : BitVec 64) :
    (htabGrowHeaderPost state table capacity keys values used order orderPos).memory (table + 16) = .word capacity ∧
    (htabGrowHeaderPost state table capacity keys values used order orderPos).memory (table + 32) = .word keys ∧
    (htabGrowHeaderPost state table capacity keys values used order orderPos).memory (table + 40) = .word values ∧
    (htabGrowHeaderPost state table capacity keys values used order orderPos).memory (table + 48) = .word used ∧
    (htabGrowHeaderPost state table capacity keys values used order orderPos).memory (table + 56) = .word order ∧
    (htabGrowHeaderPost state table capacity keys values used order orderPos).memory (table + 64) = .word orderPos ∧
    (htabGrowHeaderPost state table capacity keys values used order orderPos).memory (table + 24) = .word 0 ∧
    (htabGrowHeaderPost state table capacity keys values used order orderPos).memory (table + 0) = state.memory (table + 0) ∧
    (htabGrowHeaderPost state table capacity keys values used order orderPos).memory (table + 8) = state.memory (table + 8) := by
  simp [htabGrowHeaderPost,sourceWriteWord]

#print axioms source_htabGrow_header_stores
#print axioms evaluate_htabGrow_header
#print axioms htabGrowHeaderPost_fields
end InitECandidate.Runtime
