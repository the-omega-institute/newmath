import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RationalIntervalEnclosureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RationalIntervalEnclosureUp : Type where
  | mk
      (lower upper order dyadicTolerance source readback interval realSeal transport
        replay provenance nameCert : BHist) :
      RationalIntervalEnclosureUp
  deriving DecidableEq

def rationalIntervalEnclosureEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rationalIntervalEnclosureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rationalIntervalEnclosureEncodeBHist h

def rationalIntervalEnclosureDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rationalIntervalEnclosureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rationalIntervalEnclosureDecodeBHist tail)

private theorem RationalIntervalEnclosureTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      rationalIntervalEnclosureDecodeBHist (rationalIntervalEnclosureEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def rationalIntervalEnclosureFields :
    RationalIntervalEnclosureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RationalIntervalEnclosureUp.mk lower upper order dyadicTolerance source readback
      interval realSeal transport replay provenance nameCert =>
      [lower, upper, order, dyadicTolerance, source, readback, interval, realSeal,
        transport, replay, provenance, nameCert]

def rationalIntervalEnclosureToEventFlow :
    RationalIntervalEnclosureUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map rationalIntervalEnclosureEncodeBHist
        (rationalIntervalEnclosureFields x)

private def rationalIntervalEnclosureEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => rationalIntervalEnclosureEventAt index rest

def rationalIntervalEnclosureFromEventFlow :
    EventFlow → Option RationalIntervalEnclosureUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (RationalIntervalEnclosureUp.mk
          (rationalIntervalEnclosureDecodeBHist (rationalIntervalEnclosureEventAt 0 ef))
          (rationalIntervalEnclosureDecodeBHist (rationalIntervalEnclosureEventAt 1 ef))
          (rationalIntervalEnclosureDecodeBHist (rationalIntervalEnclosureEventAt 2 ef))
          (rationalIntervalEnclosureDecodeBHist (rationalIntervalEnclosureEventAt 3 ef))
          (rationalIntervalEnclosureDecodeBHist (rationalIntervalEnclosureEventAt 4 ef))
          (rationalIntervalEnclosureDecodeBHist (rationalIntervalEnclosureEventAt 5 ef))
          (rationalIntervalEnclosureDecodeBHist (rationalIntervalEnclosureEventAt 6 ef))
          (rationalIntervalEnclosureDecodeBHist (rationalIntervalEnclosureEventAt 7 ef))
          (rationalIntervalEnclosureDecodeBHist (rationalIntervalEnclosureEventAt 8 ef))
          (rationalIntervalEnclosureDecodeBHist (rationalIntervalEnclosureEventAt 9 ef))
          (rationalIntervalEnclosureDecodeBHist (rationalIntervalEnclosureEventAt 10 ef))
          (rationalIntervalEnclosureDecodeBHist (rationalIntervalEnclosureEventAt 11 ef)))

private theorem RationalIntervalEnclosureTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RationalIntervalEnclosureUp,
      rationalIntervalEnclosureFromEventFlow (rationalIntervalEnclosureToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk lower upper order dyadicTolerance source readback interval realSeal transport
      replay provenance nameCert =>
      change
        some
          (RationalIntervalEnclosureUp.mk
            (rationalIntervalEnclosureDecodeBHist
              (rationalIntervalEnclosureEncodeBHist lower))
            (rationalIntervalEnclosureDecodeBHist
              (rationalIntervalEnclosureEncodeBHist upper))
            (rationalIntervalEnclosureDecodeBHist
              (rationalIntervalEnclosureEncodeBHist order))
            (rationalIntervalEnclosureDecodeBHist
              (rationalIntervalEnclosureEncodeBHist dyadicTolerance))
            (rationalIntervalEnclosureDecodeBHist
              (rationalIntervalEnclosureEncodeBHist source))
            (rationalIntervalEnclosureDecodeBHist
              (rationalIntervalEnclosureEncodeBHist readback))
            (rationalIntervalEnclosureDecodeBHist
              (rationalIntervalEnclosureEncodeBHist interval))
            (rationalIntervalEnclosureDecodeBHist
              (rationalIntervalEnclosureEncodeBHist realSeal))
            (rationalIntervalEnclosureDecodeBHist
              (rationalIntervalEnclosureEncodeBHist transport))
            (rationalIntervalEnclosureDecodeBHist
              (rationalIntervalEnclosureEncodeBHist replay))
            (rationalIntervalEnclosureDecodeBHist
              (rationalIntervalEnclosureEncodeBHist provenance))
            (rationalIntervalEnclosureDecodeBHist
              (rationalIntervalEnclosureEncodeBHist nameCert))) =
          some
            (RationalIntervalEnclosureUp.mk lower upper order dyadicTolerance source
              readback interval realSeal transport replay provenance nameCert)
      rw [RationalIntervalEnclosureTasteGate_single_carrier_alignment_decode lower,
        RationalIntervalEnclosureTasteGate_single_carrier_alignment_decode upper,
        RationalIntervalEnclosureTasteGate_single_carrier_alignment_decode order,
        RationalIntervalEnclosureTasteGate_single_carrier_alignment_decode dyadicTolerance,
        RationalIntervalEnclosureTasteGate_single_carrier_alignment_decode source,
        RationalIntervalEnclosureTasteGate_single_carrier_alignment_decode readback,
        RationalIntervalEnclosureTasteGate_single_carrier_alignment_decode interval,
        RationalIntervalEnclosureTasteGate_single_carrier_alignment_decode realSeal,
        RationalIntervalEnclosureTasteGate_single_carrier_alignment_decode transport,
        RationalIntervalEnclosureTasteGate_single_carrier_alignment_decode replay,
        RationalIntervalEnclosureTasteGate_single_carrier_alignment_decode provenance,
        RationalIntervalEnclosureTasteGate_single_carrier_alignment_decode nameCert]

private theorem RationalIntervalEnclosureTasteGate_single_carrier_alignment_injective
    {x y : RationalIntervalEnclosureUp} :
    rationalIntervalEnclosureToEventFlow x = rationalIntervalEnclosureToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rationalIntervalEnclosureFromEventFlow (rationalIntervalEnclosureToEventFlow x) =
        rationalIntervalEnclosureFromEventFlow (rationalIntervalEnclosureToEventFlow y) :=
    congrArg rationalIntervalEnclosureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RationalIntervalEnclosureTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RationalIntervalEnclosureTasteGate_single_carrier_alignment_round_trip y)))

private theorem rationalIntervalEnclosure_field_faithful :
    ∀ x y : RationalIntervalEnclosureUp,
      rationalIntervalEnclosureFields x = rationalIntervalEnclosureFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk lower1 upper1 order1 dyadicTolerance1 source1 readback1 interval1 realSeal1
      transport1 replay1 provenance1 nameCert1 =>
      cases y with
      | mk lower2 upper2 order2 dyadicTolerance2 source2 readback2 interval2 realSeal2
          transport2 replay2 provenance2 nameCert2 =>
          cases h
          rfl

instance rationalIntervalEnclosureBHistCarrier :
    BHistCarrier RationalIntervalEnclosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rationalIntervalEnclosureToEventFlow
  fromEventFlow := rationalIntervalEnclosureFromEventFlow

instance rationalIntervalEnclosureChapterTasteGate :
    ChapterTasteGate RationalIntervalEnclosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      rationalIntervalEnclosureFromEventFlow (rationalIntervalEnclosureToEventFlow x) =
        some x
    exact RationalIntervalEnclosureTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RationalIntervalEnclosureTasteGate_single_carrier_alignment_injective heq)

instance rationalIntervalEnclosureFieldFaithful :
    FieldFaithful RationalIntervalEnclosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := rationalIntervalEnclosureFields
  field_faithful := rationalIntervalEnclosure_field_faithful

instance rationalIntervalEnclosureNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RationalIntervalEnclosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RationalIntervalEnclosureUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      RationalIntervalEnclosureUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RationalIntervalEnclosureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  rationalIntervalEnclosureChapterTasteGate

theorem RationalIntervalEnclosureTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      rationalIntervalEnclosureDecodeBHist (rationalIntervalEnclosureEncodeBHist h) =
        h) ∧
      (∀ x : RationalIntervalEnclosureUp,
        rationalIntervalEnclosureFromEventFlow (rationalIntervalEnclosureToEventFlow x) =
          some x) ∧
        (∀ x y : RationalIntervalEnclosureUp,
          rationalIntervalEnclosureToEventFlow x =
              rationalIntervalEnclosureToEventFlow y →
            x = y) ∧
          rationalIntervalEnclosureEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RationalIntervalEnclosureTasteGate_single_carrier_alignment_decode
  · constructor
    · exact RationalIntervalEnclosureTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact RationalIntervalEnclosureTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.RationalIntervalEnclosureUp
