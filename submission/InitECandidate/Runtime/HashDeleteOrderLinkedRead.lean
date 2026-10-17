import InitECandidate.Runtime.HashDeleteOrderLinkedMove
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

theorem HashDeleteOrderLinked.after_read {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (used order orderPos capacity items hole deletedPosition : BitVec 64)
    (linked : HashDeleteOrderLinked used order orderPos capacity items hole deletedPosition state)
    (memory : post.memory = state.memory) (domain : post.memaddrs = state.memaddrs) (endian : post.be = state.be) :
    HashDeleteOrderLinked used order orderPos capacity items hole deletedPosition post := by
  apply linked.framed state post used order orderPos capacity items hole deletedPosition
  · intro slot inside different occupied
    have same : hashOccupancyRead post used slot = hashOccupancyRead state used slot := by
      unfold hashOccupancyRead
      rw [memory,domain,endian]
    rw [← same]
    exact occupied
  · intro slot inside different; rw [memory]
  · intro position inside different; rw [memory]

#print axioms HashDeleteOrderLinked.after_read
end InitECandidate.Runtime
