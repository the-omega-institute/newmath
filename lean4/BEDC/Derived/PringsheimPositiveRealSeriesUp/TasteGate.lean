import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PringsheimPositiveRealSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PringsheimPositiveRealSeriesUp : Type where
  | mk (T S M D R E H C P N : BHist) : PringsheimPositiveRealSeriesUp
  deriving DecidableEq

def pringsheimPositiveRealSeriesEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: pringsheimPositiveRealSeriesEncodeBHist h
  | BHist.e1 h => BMark.b1 :: pringsheimPositiveRealSeriesEncodeBHist h

def pringsheimPositiveRealSeriesDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (pringsheimPositiveRealSeriesDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (pringsheimPositiveRealSeriesDecodeBHist tail)

private theorem pringsheimPositiveRealSeries_decode_encode_bhist :
    ∀ h : BHist,
      pringsheimPositiveRealSeriesDecodeBHist
        (pringsheimPositiveRealSeriesEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def pringsheimPositiveRealSeriesFields :
    PringsheimPositiveRealSeriesUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PringsheimPositiveRealSeriesUp.mk T S M D R E H C P N =>
      [T, S, M, D, R, E, H, C, P, N]

def pringsheimPositiveRealSeriesToEventFlow :
    PringsheimPositiveRealSeriesUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PringsheimPositiveRealSeriesUp.mk T S M D R E H C P N =>
      [pringsheimPositiveRealSeriesEncodeBHist T,
        pringsheimPositiveRealSeriesEncodeBHist S,
        pringsheimPositiveRealSeriesEncodeBHist M,
        pringsheimPositiveRealSeriesEncodeBHist D,
        pringsheimPositiveRealSeriesEncodeBHist R,
        pringsheimPositiveRealSeriesEncodeBHist E,
        pringsheimPositiveRealSeriesEncodeBHist H,
        pringsheimPositiveRealSeriesEncodeBHist C,
        pringsheimPositiveRealSeriesEncodeBHist P,
        pringsheimPositiveRealSeriesEncodeBHist N]

private def pringsheimPositiveRealSeriesRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => pringsheimPositiveRealSeriesRawAt n rest

private def pringsheimPositiveRealSeriesLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => pringsheimPositiveRealSeriesLengthEq n rest

def pringsheimPositiveRealSeriesFromEventFlow :
    EventFlow → Option PringsheimPositiveRealSeriesUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match pringsheimPositiveRealSeriesLengthEq 10 flow with
      | true =>
          some
            (PringsheimPositiveRealSeriesUp.mk
              (pringsheimPositiveRealSeriesDecodeBHist
                (pringsheimPositiveRealSeriesRawAt 0 flow))
              (pringsheimPositiveRealSeriesDecodeBHist
                (pringsheimPositiveRealSeriesRawAt 1 flow))
              (pringsheimPositiveRealSeriesDecodeBHist
                (pringsheimPositiveRealSeriesRawAt 2 flow))
              (pringsheimPositiveRealSeriesDecodeBHist
                (pringsheimPositiveRealSeriesRawAt 3 flow))
              (pringsheimPositiveRealSeriesDecodeBHist
                (pringsheimPositiveRealSeriesRawAt 4 flow))
              (pringsheimPositiveRealSeriesDecodeBHist
                (pringsheimPositiveRealSeriesRawAt 5 flow))
              (pringsheimPositiveRealSeriesDecodeBHist
                (pringsheimPositiveRealSeriesRawAt 6 flow))
              (pringsheimPositiveRealSeriesDecodeBHist
                (pringsheimPositiveRealSeriesRawAt 7 flow))
              (pringsheimPositiveRealSeriesDecodeBHist
                (pringsheimPositiveRealSeriesRawAt 8 flow))
              (pringsheimPositiveRealSeriesDecodeBHist
                (pringsheimPositiveRealSeriesRawAt 9 flow)))
      | false => none

private theorem pringsheimPositiveRealSeries_round_trip :
    ∀ x : PringsheimPositiveRealSeriesUp,
      pringsheimPositiveRealSeriesFromEventFlow
        (pringsheimPositiveRealSeriesToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T S M D R E H C P N =>
      change
        some
          (PringsheimPositiveRealSeriesUp.mk
            (pringsheimPositiveRealSeriesDecodeBHist
              (pringsheimPositiveRealSeriesEncodeBHist T))
            (pringsheimPositiveRealSeriesDecodeBHist
              (pringsheimPositiveRealSeriesEncodeBHist S))
            (pringsheimPositiveRealSeriesDecodeBHist
              (pringsheimPositiveRealSeriesEncodeBHist M))
            (pringsheimPositiveRealSeriesDecodeBHist
              (pringsheimPositiveRealSeriesEncodeBHist D))
            (pringsheimPositiveRealSeriesDecodeBHist
              (pringsheimPositiveRealSeriesEncodeBHist R))
            (pringsheimPositiveRealSeriesDecodeBHist
              (pringsheimPositiveRealSeriesEncodeBHist E))
            (pringsheimPositiveRealSeriesDecodeBHist
              (pringsheimPositiveRealSeriesEncodeBHist H))
            (pringsheimPositiveRealSeriesDecodeBHist
              (pringsheimPositiveRealSeriesEncodeBHist C))
            (pringsheimPositiveRealSeriesDecodeBHist
              (pringsheimPositiveRealSeriesEncodeBHist P))
            (pringsheimPositiveRealSeriesDecodeBHist
              (pringsheimPositiveRealSeriesEncodeBHist N))) =
          some (PringsheimPositiveRealSeriesUp.mk T S M D R E H C P N)
      rw [pringsheimPositiveRealSeries_decode_encode_bhist T,
        pringsheimPositiveRealSeries_decode_encode_bhist S,
        pringsheimPositiveRealSeries_decode_encode_bhist M,
        pringsheimPositiveRealSeries_decode_encode_bhist D,
        pringsheimPositiveRealSeries_decode_encode_bhist R,
        pringsheimPositiveRealSeries_decode_encode_bhist E,
        pringsheimPositiveRealSeries_decode_encode_bhist H,
        pringsheimPositiveRealSeries_decode_encode_bhist C,
        pringsheimPositiveRealSeries_decode_encode_bhist P,
        pringsheimPositiveRealSeries_decode_encode_bhist N]

private theorem pringsheimPositiveRealSeriesToEventFlow_injective
    {x y : PringsheimPositiveRealSeriesUp} :
    pringsheimPositiveRealSeriesToEventFlow x =
        pringsheimPositiveRealSeriesToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      pringsheimPositiveRealSeriesFromEventFlow
          (pringsheimPositiveRealSeriesToEventFlow x) =
        pringsheimPositiveRealSeriesFromEventFlow
          (pringsheimPositiveRealSeriesToEventFlow y) :=
    congrArg pringsheimPositiveRealSeriesFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (pringsheimPositiveRealSeries_round_trip x).symm
      (Eq.trans hread (pringsheimPositiveRealSeries_round_trip y)))

private theorem pringsheimPositiveRealSeries_field_faithful :
    ∀ x y : PringsheimPositiveRealSeriesUp,
      pringsheimPositiveRealSeriesFields x =
          pringsheimPositiveRealSeriesFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk T1 S1 M1 D1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk T2 S2 M2 D2 R2 E2 H2 C2 P2 N2 =>
          cases h
          rfl

instance pringsheimPositiveRealSeriesBHistCarrier :
    BHistCarrier PringsheimPositiveRealSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := pringsheimPositiveRealSeriesToEventFlow
  fromEventFlow := pringsheimPositiveRealSeriesFromEventFlow

instance pringsheimPositiveRealSeriesChapterTasteGate :
    ChapterTasteGate PringsheimPositiveRealSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      pringsheimPositiveRealSeriesFromEventFlow
        (pringsheimPositiveRealSeriesToEventFlow x) = some x
    exact pringsheimPositiveRealSeries_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (pringsheimPositiveRealSeriesToEventFlow_injective heq)

instance pringsheimPositiveRealSeriesFieldFaithful :
    FieldFaithful PringsheimPositiveRealSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := pringsheimPositiveRealSeriesFields
  field_faithful := pringsheimPositiveRealSeries_field_faithful

def taste_gate : ChapterTasteGate PringsheimPositiveRealSeriesUp :=
  -- BEDC touchpoint anchor: BHist BMark
  pringsheimPositiveRealSeriesChapterTasteGate

theorem PringsheimPositiveRealSeriesTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier PringsheimPositiveRealSeriesUp) ∧
      Nonempty (ChapterTasteGate PringsheimPositiveRealSeriesUp) ∧
        (∀ x : PringsheimPositiveRealSeriesUp,
          pringsheimPositiveRealSeriesFromEventFlow
              (pringsheimPositiveRealSeriesToEventFlow x) = some x) ∧
          (∀ x y : PringsheimPositiveRealSeriesUp,
            pringsheimPositiveRealSeriesToEventFlow x =
                pringsheimPositiveRealSeriesToEventFlow y →
              x = y) ∧
            pringsheimPositiveRealSeriesEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨pringsheimPositiveRealSeriesBHistCarrier⟩,
      ⟨pringsheimPositiveRealSeriesChapterTasteGate⟩,
      pringsheimPositiveRealSeries_round_trip,
      (fun _ _ heq => pringsheimPositiveRealSeriesToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.PringsheimPositiveRealSeriesUp
