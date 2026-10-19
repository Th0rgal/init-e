import InitECandidate.Runtime.WordStoreMemoryFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem evaluate_word_store_normal_memory {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (destination expression : ExpHOL 64) (address word : BitVec 64)
    (atAddress : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      destination = some (.val (.word address)))
    (atWord : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      expression = some (.val (.word word)))
    (run : evaluateHOLFiniteState s (.store destination expression) = (none,post)) :
    post.memory address = .word word ∧
      ∀ watched : BitVec 64, watched ≠ address → post.memory watched = s.memory watched := by
  rw [evaluateHOLFiniteState_store,atAddress,atWord] at run
  by_cases accessible : s.memaddrs address
  · simp [flattenHOL,panMemStoresHOL,panMemStoreHOL,accessible] at run
    subst post
    constructor
    · simp
    · intro watched separate
      simp [separate]
  · simp [flattenHOL,panMemStoresHOL,panMemStoreHOL,accessible] at run

#print axioms evaluate_word_store_normal_memory
end InitECandidate.Runtime
