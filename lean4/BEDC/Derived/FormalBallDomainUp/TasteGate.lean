import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FormalBallDomainUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FormalBallDomainUp : Type where
  | mk (X B R C E H P N : BHist) : FormalBallDomainUp
  deriving DecidableEq

private def encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: encodeBHist h
  | BHist.e1 h => BMark.b1 :: encodeBHist h

private def decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (decodeBHist tail)

private theorem decode_encodeBHist :
    ∀ h : BHist, decodeBHist (encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def eventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => eventAtDefault index rest

private def toEventFlow : FormalBallDomainUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FormalBallDomainUp.mk X B R C E H P N =>
      [[BMark.b0],
        encodeBHist X,
        [BMark.b1, BMark.b0],
        encodeBHist B,
        [BMark.b1, BMark.b1, BMark.b0],
        encodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        encodeBHist N]

private def fromEventFlow (ef : EventFlow) : Option FormalBallDomainUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FormalBallDomainUp.mk
      (decodeBHist (eventAtDefault 1 ef))
      (decodeBHist (eventAtDefault 3 ef))
      (decodeBHist (eventAtDefault 5 ef))
      (decodeBHist (eventAtDefault 7 ef))
      (decodeBHist (eventAtDefault 9 ef))
      (decodeBHist (eventAtDefault 11 ef))
      (decodeBHist (eventAtDefault 13 ef))
      (decodeBHist (eventAtDefault 15 ef)))

private theorem formalBallDomain_round_trip :
    ∀ x : FormalBallDomainUp, fromEventFlow (toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X B R C E H P N =>
      change
        some
          (FormalBallDomainUp.mk
            (decodeBHist (encodeBHist X))
            (decodeBHist (encodeBHist B))
            (decodeBHist (encodeBHist R))
            (decodeBHist (encodeBHist C))
            (decodeBHist (encodeBHist E))
            (decodeBHist (encodeBHist H))
            (decodeBHist (encodeBHist P))
            (decodeBHist (encodeBHist N))) =
          some (FormalBallDomainUp.mk X B R C E H P N)
      rw [decode_encodeBHist X, decode_encodeBHist B, decode_encodeBHist R,
        decode_encodeBHist C, decode_encodeBHist E, decode_encodeBHist H,
        decode_encodeBHist P, decode_encodeBHist N]

private theorem formalBallDomainToEventFlow_injective {x y : FormalBallDomainUp} :
    toEventFlow x = toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread : fromEventFlow (toEventFlow x) = fromEventFlow (toEventFlow y) :=
    congrArg fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (formalBallDomain_round_trip x).symm
      (Eq.trans hread (formalBallDomain_round_trip y)))

instance formalBallDomainBHistCarrier : BHistCarrier FormalBallDomainUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := toEventFlow
  fromEventFlow := fromEventFlow

instance formalBallDomainChapterTasteGate : ChapterTasteGate FormalBallDomainUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fromEventFlow (toEventFlow x) = some x
    exact formalBallDomain_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (formalBallDomainToEventFlow_injective heq)

def taste_gate : ChapterTasteGate FormalBallDomainUp :=
  -- BEDC touchpoint anchor: BHist BMark
  formalBallDomainChapterTasteGate

end BEDC.Derived.FormalBallDomainUp
