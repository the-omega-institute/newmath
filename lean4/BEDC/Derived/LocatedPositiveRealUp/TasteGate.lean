import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedPositiveRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedPositiveRealUp : Type where
  | mk (R P A L D W Q H C S N : BHist) : LocatedPositiveRealUp
  deriving DecidableEq

def locatedPositiveRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedPositiveRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedPositiveRealEncodeBHist h

def locatedPositiveRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedPositiveRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedPositiveRealDecodeBHist tail)

private theorem LocatedPositiveRealTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, locatedPositiveRealDecodeBHist (locatedPositiveRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedPositiveRealFields : LocatedPositiveRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedPositiveRealUp.mk R P A L D W Q H C S N => [R, P, A, L, D, W, Q, H, C, S, N]

def locatedPositiveRealToEventFlow : LocatedPositiveRealUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (locatedPositiveRealFields x).map locatedPositiveRealEncodeBHist

private def locatedPositiveRealRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedPositiveRealRawAt index rest

def locatedPositiveRealFromEventFlow (flow : EventFlow) : Option LocatedPositiveRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedPositiveRealUp.mk
      (locatedPositiveRealDecodeBHist (locatedPositiveRealRawAt 0 flow))
      (locatedPositiveRealDecodeBHist (locatedPositiveRealRawAt 1 flow))
      (locatedPositiveRealDecodeBHist (locatedPositiveRealRawAt 2 flow))
      (locatedPositiveRealDecodeBHist (locatedPositiveRealRawAt 3 flow))
      (locatedPositiveRealDecodeBHist (locatedPositiveRealRawAt 4 flow))
      (locatedPositiveRealDecodeBHist (locatedPositiveRealRawAt 5 flow))
      (locatedPositiveRealDecodeBHist (locatedPositiveRealRawAt 6 flow))
      (locatedPositiveRealDecodeBHist (locatedPositiveRealRawAt 7 flow))
      (locatedPositiveRealDecodeBHist (locatedPositiveRealRawAt 8 flow))
      (locatedPositiveRealDecodeBHist (locatedPositiveRealRawAt 9 flow))
      (locatedPositiveRealDecodeBHist (locatedPositiveRealRawAt 10 flow)))

private theorem LocatedPositiveRealTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedPositiveRealUp,
      locatedPositiveRealFromEventFlow (locatedPositiveRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk R P A L D W Q H C S N =>
      change
        some
          (LocatedPositiveRealUp.mk
            (locatedPositiveRealDecodeBHist (locatedPositiveRealEncodeBHist R))
            (locatedPositiveRealDecodeBHist (locatedPositiveRealEncodeBHist P))
            (locatedPositiveRealDecodeBHist (locatedPositiveRealEncodeBHist A))
            (locatedPositiveRealDecodeBHist (locatedPositiveRealEncodeBHist L))
            (locatedPositiveRealDecodeBHist (locatedPositiveRealEncodeBHist D))
            (locatedPositiveRealDecodeBHist (locatedPositiveRealEncodeBHist W))
            (locatedPositiveRealDecodeBHist (locatedPositiveRealEncodeBHist Q))
            (locatedPositiveRealDecodeBHist (locatedPositiveRealEncodeBHist H))
            (locatedPositiveRealDecodeBHist (locatedPositiveRealEncodeBHist C))
            (locatedPositiveRealDecodeBHist (locatedPositiveRealEncodeBHist S))
            (locatedPositiveRealDecodeBHist (locatedPositiveRealEncodeBHist N))) =
          some (LocatedPositiveRealUp.mk R P A L D W Q H C S N)
      rw [LocatedPositiveRealTasteGate_single_carrier_alignment_decode R,
        LocatedPositiveRealTasteGate_single_carrier_alignment_decode P,
        LocatedPositiveRealTasteGate_single_carrier_alignment_decode A,
        LocatedPositiveRealTasteGate_single_carrier_alignment_decode L,
        LocatedPositiveRealTasteGate_single_carrier_alignment_decode D,
        LocatedPositiveRealTasteGate_single_carrier_alignment_decode W,
        LocatedPositiveRealTasteGate_single_carrier_alignment_decode Q,
        LocatedPositiveRealTasteGate_single_carrier_alignment_decode H,
        LocatedPositiveRealTasteGate_single_carrier_alignment_decode C,
        LocatedPositiveRealTasteGate_single_carrier_alignment_decode S,
        LocatedPositiveRealTasteGate_single_carrier_alignment_decode N]

private theorem locatedPositiveRealToEventFlow_injective {x y : LocatedPositiveRealUp} :
    locatedPositiveRealToEventFlow x = locatedPositiveRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedPositiveRealFromEventFlow (locatedPositiveRealToEventFlow x) =
        locatedPositiveRealFromEventFlow (locatedPositiveRealToEventFlow y) :=
    congrArg locatedPositiveRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedPositiveRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LocatedPositiveRealTasteGate_single_carrier_alignment_round_trip y)))

instance locatedPositiveRealBHistCarrier : BHistCarrier LocatedPositiveRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedPositiveRealToEventFlow
  fromEventFlow := locatedPositiveRealFromEventFlow

instance locatedPositiveRealChapterTasteGate : ChapterTasteGate LocatedPositiveRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedPositiveRealFromEventFlow (locatedPositiveRealToEventFlow x) = some x
    exact LocatedPositiveRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedPositiveRealToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedPositiveRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedPositiveRealChapterTasteGate

theorem LocatedPositiveRealTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedPositiveRealDecodeBHist (locatedPositiveRealEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LocatedPositiveRealUp) ∧
        Nonempty (ChapterTasteGate LocatedPositiveRealUp) ∧
          locatedPositiveRealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨LocatedPositiveRealTasteGate_single_carrier_alignment_decode,
      ⟨locatedPositiveRealBHistCarrier⟩,
      ⟨locatedPositiveRealChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.LocatedPositiveRealUp
