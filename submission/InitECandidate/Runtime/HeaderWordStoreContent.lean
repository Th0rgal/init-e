import InitECandidate.Runtime.HeaderWordStoreReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem header_word_store_content {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (record value : BitVec 64) (offset : Nat) (name : MlS)
    (atRecord : s.locals.lookup (ofString "h") = some (.val (.word record)))
    (atValue : s.locals.lookup name = some (.val (.word value)))
    (normal : evaluateHOLFiniteState s (headerWordStore name offset) = (none,post)) :
    post.memaddrs (record + BitVec.ofNat 64 offset) ∧ post.memory (record + BitVec.ofNat 64 offset) = .word value := by
  have dest : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "h"),.const (BitVec.ofNat 64 offset)]) =
      some (.val (.word (record + BitVec.ofNat 64 offset))) := by
    simp [evalHOLExact,evalListHOLExact,atRecord,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord]
  unfold headerWordStore at normal
  rw [evaluateHOLFiniteState_store,dest] at normal
  simp only [evalHOLExact,atValue] at normal
  by_cases accessible : s.memaddrs (record + BitVec.ofNat 64 offset)
  · simp [flattenHOL,panMemStoresHOL,panMemStoreHOL,accessible] at normal
    subst post
    simp [accessible]
  · simp [flattenHOL,panMemStoresHOL,panMemStoreHOL,accessible] at normal

#print axioms header_word_store_content
end InitECandidate.Runtime
