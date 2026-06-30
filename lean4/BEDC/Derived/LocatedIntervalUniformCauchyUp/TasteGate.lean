import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedIntervalUniformCauchyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedIntervalUniformCauchyUp : Type where
  | mk
      (locatedEndpoint locatedInterval compactInterval window readback tolerance modulus sealRow
        transport route provenance nameRow : BHist) :
      LocatedIntervalUniformCauchyUp
  deriving DecidableEq

def locatedIntervalUniformCauchyEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedIntervalUniformCauchyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedIntervalUniformCauchyEncodeBHist h

def locatedIntervalUniformCauchyDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedIntervalUniformCauchyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedIntervalUniformCauchyDecodeBHist tail)

private theorem LocatedIntervalUniformCauchyTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      locatedIntervalUniformCauchyDecodeBHist
          (locatedIntervalUniformCauchyEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedIntervalUniformCauchyFields :
    LocatedIntervalUniformCauchyUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedIntervalUniformCauchyUp.mk locatedEndpoint locatedInterval compactInterval window
      readback tolerance modulus sealRow transport route provenance nameRow =>
      [locatedEndpoint, locatedInterval, compactInterval, window, readback, tolerance, modulus,
        sealRow, transport, route, provenance, nameRow]

def locatedIntervalUniformCauchyToEventFlow :
    LocatedIntervalUniformCauchyUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (locatedIntervalUniformCauchyFields x).map
        locatedIntervalUniformCauchyEncodeBHist

private def locatedIntervalUniformCauchyEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedIntervalUniformCauchyEventAt index rest

def locatedIntervalUniformCauchyFromEventFlow
    (ef : EventFlow) : Option LocatedIntervalUniformCauchyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedIntervalUniformCauchyUp.mk
      (locatedIntervalUniformCauchyDecodeBHist
        (locatedIntervalUniformCauchyEventAt 0 ef))
      (locatedIntervalUniformCauchyDecodeBHist
        (locatedIntervalUniformCauchyEventAt 1 ef))
      (locatedIntervalUniformCauchyDecodeBHist
        (locatedIntervalUniformCauchyEventAt 2 ef))
      (locatedIntervalUniformCauchyDecodeBHist
        (locatedIntervalUniformCauchyEventAt 3 ef))
      (locatedIntervalUniformCauchyDecodeBHist
        (locatedIntervalUniformCauchyEventAt 4 ef))
      (locatedIntervalUniformCauchyDecodeBHist
        (locatedIntervalUniformCauchyEventAt 5 ef))
      (locatedIntervalUniformCauchyDecodeBHist
        (locatedIntervalUniformCauchyEventAt 6 ef))
      (locatedIntervalUniformCauchyDecodeBHist
        (locatedIntervalUniformCauchyEventAt 7 ef))
      (locatedIntervalUniformCauchyDecodeBHist
        (locatedIntervalUniformCauchyEventAt 8 ef))
      (locatedIntervalUniformCauchyDecodeBHist
        (locatedIntervalUniformCauchyEventAt 9 ef))
      (locatedIntervalUniformCauchyDecodeBHist
        (locatedIntervalUniformCauchyEventAt 10 ef))
      (locatedIntervalUniformCauchyDecodeBHist
        (locatedIntervalUniformCauchyEventAt 11 ef)))

private theorem LocatedIntervalUniformCauchyTasteGate_single_carrier_alignment_round_trip
    (x : LocatedIntervalUniformCauchyUp) :
    locatedIntervalUniformCauchyFromEventFlow
        (locatedIntervalUniformCauchyToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk locatedEndpoint locatedInterval compactInterval window readback tolerance modulus sealRow
      transport route provenance nameRow =>
      change
        some
          (LocatedIntervalUniformCauchyUp.mk
            (locatedIntervalUniformCauchyDecodeBHist
              (locatedIntervalUniformCauchyEncodeBHist locatedEndpoint))
            (locatedIntervalUniformCauchyDecodeBHist
              (locatedIntervalUniformCauchyEncodeBHist locatedInterval))
            (locatedIntervalUniformCauchyDecodeBHist
              (locatedIntervalUniformCauchyEncodeBHist compactInterval))
            (locatedIntervalUniformCauchyDecodeBHist
              (locatedIntervalUniformCauchyEncodeBHist window))
            (locatedIntervalUniformCauchyDecodeBHist
              (locatedIntervalUniformCauchyEncodeBHist readback))
            (locatedIntervalUniformCauchyDecodeBHist
              (locatedIntervalUniformCauchyEncodeBHist tolerance))
            (locatedIntervalUniformCauchyDecodeBHist
              (locatedIntervalUniformCauchyEncodeBHist modulus))
            (locatedIntervalUniformCauchyDecodeBHist
              (locatedIntervalUniformCauchyEncodeBHist sealRow))
            (locatedIntervalUniformCauchyDecodeBHist
              (locatedIntervalUniformCauchyEncodeBHist transport))
            (locatedIntervalUniformCauchyDecodeBHist
              (locatedIntervalUniformCauchyEncodeBHist route))
            (locatedIntervalUniformCauchyDecodeBHist
              (locatedIntervalUniformCauchyEncodeBHist provenance))
            (locatedIntervalUniformCauchyDecodeBHist
              (locatedIntervalUniformCauchyEncodeBHist nameRow))) =
          some
            (LocatedIntervalUniformCauchyUp.mk locatedEndpoint locatedInterval compactInterval
              window readback tolerance modulus sealRow transport route provenance nameRow)
      rw [LocatedIntervalUniformCauchyTasteGate_single_carrier_alignment_decode_encode
          locatedEndpoint,
        LocatedIntervalUniformCauchyTasteGate_single_carrier_alignment_decode_encode
          locatedInterval,
        LocatedIntervalUniformCauchyTasteGate_single_carrier_alignment_decode_encode
          compactInterval,
        LocatedIntervalUniformCauchyTasteGate_single_carrier_alignment_decode_encode window,
        LocatedIntervalUniformCauchyTasteGate_single_carrier_alignment_decode_encode readback,
        LocatedIntervalUniformCauchyTasteGate_single_carrier_alignment_decode_encode tolerance,
        LocatedIntervalUniformCauchyTasteGate_single_carrier_alignment_decode_encode modulus,
        LocatedIntervalUniformCauchyTasteGate_single_carrier_alignment_decode_encode sealRow,
        LocatedIntervalUniformCauchyTasteGate_single_carrier_alignment_decode_encode transport,
        LocatedIntervalUniformCauchyTasteGate_single_carrier_alignment_decode_encode route,
        LocatedIntervalUniformCauchyTasteGate_single_carrier_alignment_decode_encode provenance,
        LocatedIntervalUniformCauchyTasteGate_single_carrier_alignment_decode_encode nameRow]

private theorem LocatedIntervalUniformCauchyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedIntervalUniformCauchyUp} :
    locatedIntervalUniformCauchyToEventFlow x =
        locatedIntervalUniformCauchyToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedIntervalUniformCauchyFromEventFlow
          (locatedIntervalUniformCauchyToEventFlow x) =
        locatedIntervalUniformCauchyFromEventFlow
          (locatedIntervalUniformCauchyToEventFlow y) :=
    congrArg locatedIntervalUniformCauchyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedIntervalUniformCauchyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedIntervalUniformCauchyTasteGate_single_carrier_alignment_round_trip y)))

instance locatedIntervalUniformCauchyBHistCarrier :
    BHistCarrier LocatedIntervalUniformCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedIntervalUniformCauchyToEventFlow
  fromEventFlow := locatedIntervalUniformCauchyFromEventFlow

instance locatedIntervalUniformCauchyChapterTasteGate :
    ChapterTasteGate LocatedIntervalUniformCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedIntervalUniformCauchyFromEventFlow
          (locatedIntervalUniformCauchyToEventFlow x) =
        some x
    exact LocatedIntervalUniformCauchyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LocatedIntervalUniformCauchyTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem LocatedIntervalUniformCauchyTasteGate_single_carrier_alignment :
    (forall h : BHist,
        locatedIntervalUniformCauchyDecodeBHist
            (locatedIntervalUniformCauchyEncodeBHist h) =
          h) ∧
      Nonempty (BHistCarrier LocatedIntervalUniformCauchyUp) ∧
        Nonempty (ChapterTasteGate LocatedIntervalUniformCauchyUp) ∧
          locatedIntervalUniformCauchyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨LocatedIntervalUniformCauchyTasteGate_single_carrier_alignment_decode_encode,
      ⟨locatedIntervalUniformCauchyBHistCarrier⟩,
      ⟨locatedIntervalUniformCauchyChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.LocatedIntervalUniformCauchyUp
