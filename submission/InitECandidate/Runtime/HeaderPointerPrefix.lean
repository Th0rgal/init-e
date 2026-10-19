import InitECandidate.Runtime.ValidateHeadersStoreContent
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The initialized part of the actual header-pointer buffer. -/
def HeaderPointerPrefix {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hs : BitVec 64) (count : Nat) : Prop :=
  ∀ slot : BitVec 64, slot.toNat < count →
    s.memaddrs (hs + slot * (8#64)) ∧ ∃ header : BitVec 64,
      s.memory (hs + slot * (8#64)) = .word header

theorem headerPointerPrefix_empty {F : Type} (s : PanSemStateFiniteExact 64 F) (hs : BitVec 64) :
    HeaderPointerPrefix s hs 0 := by intro slot inside; omega

/-- An actual successful iteration store extends the initialized pointer
prefix by one; no earlier pointer is overwritten. -/
theorem headerPointerPrefix_store {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (hs index header : BitVec 64)
    (initialized : HeaderPointerPrefix s hs index.toNat)
    (fits : index.toNat * 8 < 2^64)
    (atHs : s.locals.lookup (ofString "hs") = some (.val (.word hs)))
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (atHeader : s.locals.lookup (ofString "h") = some (.val (.word header)))
    (normal : evaluateHOLFiniteState s validateHeadersHeaderStore = (none,post)) :
    HeaderPointerPrefix post hs (index.toNat + 1) := by
  intro slot inside
  by_cases same : slot = index
  · subst slot
    obtain ⟨domain,word⟩ := validate_headers_store_content s post hs index header atHs atIndex atHeader normal
    exact ⟨domain,header,word⟩
  · have older : slot.toNat < index.toNat := by
      have different : slot.toNat ≠ index.toNat := fun eq => same (BitVec.eq_of_toNat_eq eq)
      omega
    obtain ⟨domain,previous,word⟩ := initialized slot older
    have separate : hs + slot * (8#64) ≠ hs + index * (8#64) := by
      intro eq
      have cancelled : slot * (8#64) = index * (8#64) := by
        have subtracted := congrArg (fun x : BitVec 64 => x - hs) eq
        simpa [BitVec.add_comm] using subtracted
      have products := congrArg BitVec.toNat cancelled
      rw [BitVec.toNat_mul_of_lt (by change slot.toNat * 8 < 2^64; omega),
        BitVec.toNat_mul_of_lt fits] at products
      change slot.toNat * 8 = index.toNat * 8 at products
      omega
    have frame := evaluate_wordStore_memory_frame s
      (.op .add [.var .local (ofString "hs"),.panop .mul [.var .local (ofString "i"),.const 8]])
      (.var .local (ofString "h")) (hs + index * (8#64))
      (hs + slot * (8#64))
      (by simp [evalHOLExact,evalListHOLExact,atHs,atIndex,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord])
      (by intro parsed evaluated; exact ⟨header,by simpa [evalHOLExact,atHeader] using evaluated.symm⟩) separate
    change (evaluateHOLFiniteState s validateHeadersHeaderStore).2.memory _ = _ at frame
    rw [normal] at frame
    have metadata := evaluateHOLFiniteState_metadata s validateHeadersHeaderStore
    rw [normal] at metadata
    exact ⟨by rw [metadata.2.1]; exact domain,previous,frame.trans word⟩

#print axioms headerPointerPrefix_empty
#print axioms headerPointerPrefix_store

/-- A frame on initialized pointer cells transports the whole prefix across
decoder/hash calls and scope restoration. -/
theorem HeaderPointerPrefix.after_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (hs : BitVec 64) (count : Nat) (initialized : HeaderPointerPrefix s hs count)
    (domain : post.memaddrs = s.memaddrs)
    (memory : ∀ slot : BitVec 64, slot.toNat < count →
      post.memory (hs + slot * (8#64)) = s.memory (hs + slot * (8#64))) :
    HeaderPointerPrefix post hs count := by
  intro slot inside
  obtain ⟨readable,header,word⟩ := initialized slot inside
  exact ⟨by rw [domain]; exact readable,header,(memory slot inside).trans word⟩

/-- A nonempty initialized buffer supplies the last pointer cell read by
the actual `run_attempt` parent declaration. -/
theorem HeaderPointerPrefix.last {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hs count : BitVec 64) (initialized : HeaderPointerPrefix s hs count.toNat)
    (nonzero : count ≠ 0) :
    s.memaddrs (hs + (count - 1) * 8) ∧ ∃ header : BitVec 64,
      s.memory (hs + (count - 1) * 8) = .word header := by
  have positive : 0 < count.toNat := by
    have nz : count.toNat ≠ 0 := by
      intro eq
      apply nonzero
      exact BitVec.eq_of_toNat_eq eq
    omega
  have indexNat : (count - (1#64)).toNat = count.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (by change (1#64 : BitVec 64).toNat ≤ count.toNat; exact positive)]
    rfl
  exact initialized (count - (1#64)) (by rw [indexNat]; omega)

#print axioms HeaderPointerPrefix.after_frame
#print axioms HeaderPointerPrefix.last
end InitECandidate.Runtime
