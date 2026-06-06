import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyFiniteSumUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyFiniteSumUp : Type where
  | mk
      (index source windows dyadic addition readback real transport replay provenance
        localName : BHist) : RegularCauchyFiniteSumUp
  deriving DecidableEq

def regularCauchyFiniteSumEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyFiniteSumEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyFiniteSumEncodeBHist h

def regularCauchyFiniteSumDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyFiniteSumDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyFiniteSumDecodeBHist tail)

private theorem RegularCauchyFiniteSumTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      regularCauchyFiniteSumDecodeBHist (regularCauchyFiniteSumEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyFiniteSumFields : RegularCauchyFiniteSumUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyFiniteSumUp.mk index source windows dyadic addition readback real
      transport replay provenance localName =>
      [index, source, windows, dyadic, addition, readback, real, transport, replay,
        provenance, localName]

def regularCauchyFiniteSumToEventFlow : RegularCauchyFiniteSumUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (regularCauchyFiniteSumFields x).map regularCauchyFiniteSumEncodeBHist

private def regularCauchyFiniteSumEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyFiniteSumEventAtDefault index rest

def regularCauchyFiniteSumFromEventFlow
    (ef : EventFlow) : Option RegularCauchyFiniteSumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyFiniteSumUp.mk
      (regularCauchyFiniteSumDecodeBHist (regularCauchyFiniteSumEventAtDefault 0 ef))
      (regularCauchyFiniteSumDecodeBHist (regularCauchyFiniteSumEventAtDefault 1 ef))
      (regularCauchyFiniteSumDecodeBHist (regularCauchyFiniteSumEventAtDefault 2 ef))
      (regularCauchyFiniteSumDecodeBHist (regularCauchyFiniteSumEventAtDefault 3 ef))
      (regularCauchyFiniteSumDecodeBHist (regularCauchyFiniteSumEventAtDefault 4 ef))
      (regularCauchyFiniteSumDecodeBHist (regularCauchyFiniteSumEventAtDefault 5 ef))
      (regularCauchyFiniteSumDecodeBHist (regularCauchyFiniteSumEventAtDefault 6 ef))
      (regularCauchyFiniteSumDecodeBHist (regularCauchyFiniteSumEventAtDefault 7 ef))
      (regularCauchyFiniteSumDecodeBHist (regularCauchyFiniteSumEventAtDefault 8 ef))
      (regularCauchyFiniteSumDecodeBHist (regularCauchyFiniteSumEventAtDefault 9 ef))
      (regularCauchyFiniteSumDecodeBHist (regularCauchyFiniteSumEventAtDefault 10 ef)))

private theorem RegularCauchyFiniteSumTasteGate_single_carrier_alignment_round_trip
    (x : RegularCauchyFiniteSumUp) :
    regularCauchyFiniteSumFromEventFlow (regularCauchyFiniteSumToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk index source windows dyadic addition readback real transport replay provenance
      localName =>
      change
        some
          (RegularCauchyFiniteSumUp.mk
            (regularCauchyFiniteSumDecodeBHist
              (regularCauchyFiniteSumEncodeBHist index))
            (regularCauchyFiniteSumDecodeBHist
              (regularCauchyFiniteSumEncodeBHist source))
            (regularCauchyFiniteSumDecodeBHist
              (regularCauchyFiniteSumEncodeBHist windows))
            (regularCauchyFiniteSumDecodeBHist
              (regularCauchyFiniteSumEncodeBHist dyadic))
            (regularCauchyFiniteSumDecodeBHist
              (regularCauchyFiniteSumEncodeBHist addition))
            (regularCauchyFiniteSumDecodeBHist
              (regularCauchyFiniteSumEncodeBHist readback))
            (regularCauchyFiniteSumDecodeBHist
              (regularCauchyFiniteSumEncodeBHist real))
            (regularCauchyFiniteSumDecodeBHist
              (regularCauchyFiniteSumEncodeBHist transport))
            (regularCauchyFiniteSumDecodeBHist
              (regularCauchyFiniteSumEncodeBHist replay))
            (regularCauchyFiniteSumDecodeBHist
              (regularCauchyFiniteSumEncodeBHist provenance))
            (regularCauchyFiniteSumDecodeBHist
              (regularCauchyFiniteSumEncodeBHist localName))) =
          some
            (RegularCauchyFiniteSumUp.mk index source windows dyadic addition readback
              real transport replay provenance localName)
      rw [RegularCauchyFiniteSumTasteGate_single_carrier_alignment_decode index,
        RegularCauchyFiniteSumTasteGate_single_carrier_alignment_decode source,
        RegularCauchyFiniteSumTasteGate_single_carrier_alignment_decode windows,
        RegularCauchyFiniteSumTasteGate_single_carrier_alignment_decode dyadic,
        RegularCauchyFiniteSumTasteGate_single_carrier_alignment_decode addition,
        RegularCauchyFiniteSumTasteGate_single_carrier_alignment_decode readback,
        RegularCauchyFiniteSumTasteGate_single_carrier_alignment_decode real,
        RegularCauchyFiniteSumTasteGate_single_carrier_alignment_decode transport,
        RegularCauchyFiniteSumTasteGate_single_carrier_alignment_decode replay,
        RegularCauchyFiniteSumTasteGate_single_carrier_alignment_decode provenance,
        RegularCauchyFiniteSumTasteGate_single_carrier_alignment_decode localName]

private theorem RegularCauchyFiniteSumTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyFiniteSumUp} :
    regularCauchyFiniteSumToEventFlow x = regularCauchyFiniteSumToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyFiniteSumFromEventFlow (regularCauchyFiniteSumToEventFlow x) =
        regularCauchyFiniteSumFromEventFlow (regularCauchyFiniteSumToEventFlow y) :=
    congrArg regularCauchyFiniteSumFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularCauchyFiniteSumTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyFiniteSumTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyFiniteSumBHistCarrier :
    BHistCarrier RegularCauchyFiniteSumUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyFiniteSumToEventFlow
  fromEventFlow := regularCauchyFiniteSumFromEventFlow

instance regularCauchyFiniteSumChapterTasteGate :
    ChapterTasteGate RegularCauchyFiniteSumUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyFiniteSumFromEventFlow (regularCauchyFiniteSumToEventFlow x) =
        some x
    exact RegularCauchyFiniteSumTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyFiniteSumTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyFiniteSumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyFiniteSumChapterTasteGate

theorem RegularCauchyFiniteSumTasteGate_single_carrier_alignment
    (x : RegularCauchyFiniteSumUp) :
    (exists index source windows dyadic addition readback real transport replay provenance
        localName : BHist,
      x =
        RegularCauchyFiniteSumUp.mk index source windows dyadic addition readback real
          transport replay provenance localName) ∧
      Nonempty (BHistCarrier RegularCauchyFiniteSumUp) ∧
        Nonempty (ChapterTasteGate RegularCauchyFiniteSumUp) ∧
          regularCauchyFiniteSumEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk index source windows dyadic addition readback real transport replay provenance
      localName =>
      exact
        ⟨⟨index, source, windows, dyadic, addition, readback, real, transport, replay,
            provenance, localName, rfl⟩,
          ⟨regularCauchyFiniteSumBHistCarrier⟩,
          ⟨regularCauchyFiniteSumChapterTasteGate⟩,
          rfl⟩

end BEDC.Derived.RegularCauchyFiniteSumUp
