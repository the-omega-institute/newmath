import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CommutativeCStarUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CommutativeCStarUp : Type where
  | mk (A B R I M E Q L X T Y H C P N : BHist) : CommutativeCStarUp
  deriving DecidableEq

def commutativeCStarEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: commutativeCStarEncodeBHist h
  | BHist.e1 h => BMark.b1 :: commutativeCStarEncodeBHist h

def commutativeCStarDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (commutativeCStarDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (commutativeCStarDecodeBHist tail)

private theorem CommutativeCStarTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, commutativeCStarDecodeBHist (commutativeCStarEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def commutativeCStarFields : CommutativeCStarUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CommutativeCStarUp.mk A B R I M E Q L X T Y H C P N =>
      [A, B, R, I, M, E, Q, L, X, T, Y, H, C, P, N]

def commutativeCStarToEventFlow : CommutativeCStarUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token => (commutativeCStarFields token).map commutativeCStarEncodeBHist

private def commutativeCStarEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => commutativeCStarEventAtDefault index rest

def commutativeCStarFromEventFlow (ef : EventFlow) : Option CommutativeCStarUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CommutativeCStarUp.mk
      (commutativeCStarDecodeBHist (commutativeCStarEventAtDefault 0 ef))
      (commutativeCStarDecodeBHist (commutativeCStarEventAtDefault 1 ef))
      (commutativeCStarDecodeBHist (commutativeCStarEventAtDefault 2 ef))
      (commutativeCStarDecodeBHist (commutativeCStarEventAtDefault 3 ef))
      (commutativeCStarDecodeBHist (commutativeCStarEventAtDefault 4 ef))
      (commutativeCStarDecodeBHist (commutativeCStarEventAtDefault 5 ef))
      (commutativeCStarDecodeBHist (commutativeCStarEventAtDefault 6 ef))
      (commutativeCStarDecodeBHist (commutativeCStarEventAtDefault 7 ef))
      (commutativeCStarDecodeBHist (commutativeCStarEventAtDefault 8 ef))
      (commutativeCStarDecodeBHist (commutativeCStarEventAtDefault 9 ef))
      (commutativeCStarDecodeBHist (commutativeCStarEventAtDefault 10 ef))
      (commutativeCStarDecodeBHist (commutativeCStarEventAtDefault 11 ef))
      (commutativeCStarDecodeBHist (commutativeCStarEventAtDefault 12 ef))
      (commutativeCStarDecodeBHist (commutativeCStarEventAtDefault 13 ef))
      (commutativeCStarDecodeBHist (commutativeCStarEventAtDefault 14 ef)))

private theorem CommutativeCStarTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CommutativeCStarUp,
      commutativeCStarFromEventFlow (commutativeCStarToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk A B R I M E Q L X T Y H C P N =>
      change
        some
          (CommutativeCStarUp.mk
            (commutativeCStarDecodeBHist (commutativeCStarEncodeBHist A))
            (commutativeCStarDecodeBHist (commutativeCStarEncodeBHist B))
            (commutativeCStarDecodeBHist (commutativeCStarEncodeBHist R))
            (commutativeCStarDecodeBHist (commutativeCStarEncodeBHist I))
            (commutativeCStarDecodeBHist (commutativeCStarEncodeBHist M))
            (commutativeCStarDecodeBHist (commutativeCStarEncodeBHist E))
            (commutativeCStarDecodeBHist (commutativeCStarEncodeBHist Q))
            (commutativeCStarDecodeBHist (commutativeCStarEncodeBHist L))
            (commutativeCStarDecodeBHist (commutativeCStarEncodeBHist X))
            (commutativeCStarDecodeBHist (commutativeCStarEncodeBHist T))
            (commutativeCStarDecodeBHist (commutativeCStarEncodeBHist Y))
            (commutativeCStarDecodeBHist (commutativeCStarEncodeBHist H))
            (commutativeCStarDecodeBHist (commutativeCStarEncodeBHist C))
            (commutativeCStarDecodeBHist (commutativeCStarEncodeBHist P))
            (commutativeCStarDecodeBHist (commutativeCStarEncodeBHist N))) =
          some (CommutativeCStarUp.mk A B R I M E Q L X T Y H C P N)
      rw [CommutativeCStarTasteGate_single_carrier_alignment_decode A,
        CommutativeCStarTasteGate_single_carrier_alignment_decode B,
        CommutativeCStarTasteGate_single_carrier_alignment_decode R,
        CommutativeCStarTasteGate_single_carrier_alignment_decode I,
        CommutativeCStarTasteGate_single_carrier_alignment_decode M,
        CommutativeCStarTasteGate_single_carrier_alignment_decode E,
        CommutativeCStarTasteGate_single_carrier_alignment_decode Q,
        CommutativeCStarTasteGate_single_carrier_alignment_decode L,
        CommutativeCStarTasteGate_single_carrier_alignment_decode X,
        CommutativeCStarTasteGate_single_carrier_alignment_decode T,
        CommutativeCStarTasteGate_single_carrier_alignment_decode Y,
        CommutativeCStarTasteGate_single_carrier_alignment_decode H,
        CommutativeCStarTasteGate_single_carrier_alignment_decode C,
        CommutativeCStarTasteGate_single_carrier_alignment_decode P,
        CommutativeCStarTasteGate_single_carrier_alignment_decode N]

private theorem CommutativeCStarTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CommutativeCStarUp} :
    commutativeCStarToEventFlow x = commutativeCStarToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      commutativeCStarFromEventFlow (commutativeCStarToEventFlow x) =
        commutativeCStarFromEventFlow (commutativeCStarToEventFlow y) :=
    congrArg commutativeCStarFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CommutativeCStarTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CommutativeCStarTasteGate_single_carrier_alignment_round_trip y)))

instance commutativeCStarBHistCarrier : BHistCarrier CommutativeCStarUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := commutativeCStarToEventFlow
  fromEventFlow := commutativeCStarFromEventFlow

instance commutativeCStarChapterTasteGate : ChapterTasteGate CommutativeCStarUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change commutativeCStarFromEventFlow (commutativeCStarToEventFlow x) = some x
    exact CommutativeCStarTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CommutativeCStarTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CommutativeCStarTasteGate_single_carrier_alignment :
    commutativeCStarEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
      (∀ h : BHist, commutativeCStarDecodeBHist (commutativeCStarEncodeBHist h) = h) ∧
        (∀ x : CommutativeCStarUp,
          commutativeCStarFromEventFlow (commutativeCStarToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨rfl, CommutativeCStarTasteGate_single_carrier_alignment_decode,
      CommutativeCStarTasteGate_single_carrier_alignment_round_trip⟩

end BEDC.Derived.CommutativeCStarUp.TasteGate
