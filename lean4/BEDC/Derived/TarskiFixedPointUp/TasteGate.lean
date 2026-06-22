import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TarskiFixedPointUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TarskiFixedPointUp : Type where
  | mk
      (carrier order monotone prefixRow postfixRow iteration fixed transport replay provenance
        localName : BHist) :
      TarskiFixedPointUp
  deriving DecidableEq

def tarskiFixedPointEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: tarskiFixedPointEncodeBHist h
  | BHist.e1 h => BMark.b1 :: tarskiFixedPointEncodeBHist h

def tarskiFixedPointDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (tarskiFixedPointDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (tarskiFixedPointDecodeBHist tail)

private theorem TarskiFixedPointTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, tarskiFixedPointDecodeBHist (tarskiFixedPointEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def tarskiFixedPointFields : TarskiFixedPointUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TarskiFixedPointUp.mk carrier order monotone prefixRow postfixRow iteration fixed transport replay
      provenance localName =>
      [carrier, order, monotone, prefixRow, postfixRow, iteration, fixed, transport, replay,
        provenance, localName]

def tarskiFixedPointToEventFlow : TarskiFixedPointUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (tarskiFixedPointFields x).map tarskiFixedPointEncodeBHist

private def tarskiFixedPointEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => tarskiFixedPointEventAtDefault index rest

def tarskiFixedPointFromEventFlow : EventFlow → Option TarskiFixedPointUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (TarskiFixedPointUp.mk
        (tarskiFixedPointDecodeBHist (tarskiFixedPointEventAtDefault 0 ef))
        (tarskiFixedPointDecodeBHist (tarskiFixedPointEventAtDefault 1 ef))
        (tarskiFixedPointDecodeBHist (tarskiFixedPointEventAtDefault 2 ef))
        (tarskiFixedPointDecodeBHist (tarskiFixedPointEventAtDefault 3 ef))
        (tarskiFixedPointDecodeBHist (tarskiFixedPointEventAtDefault 4 ef))
        (tarskiFixedPointDecodeBHist (tarskiFixedPointEventAtDefault 5 ef))
        (tarskiFixedPointDecodeBHist (tarskiFixedPointEventAtDefault 6 ef))
        (tarskiFixedPointDecodeBHist (tarskiFixedPointEventAtDefault 7 ef))
        (tarskiFixedPointDecodeBHist (tarskiFixedPointEventAtDefault 8 ef))
        (tarskiFixedPointDecodeBHist (tarskiFixedPointEventAtDefault 9 ef))
        (tarskiFixedPointDecodeBHist (tarskiFixedPointEventAtDefault 10 ef)))

private theorem TarskiFixedPointTasteGate_single_carrier_alignment_round_trip :
    ∀ x : TarskiFixedPointUp,
      tarskiFixedPointFromEventFlow (tarskiFixedPointToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk carrier order monotone prefixRow postfixRow iteration fixed transport replay provenance localName =>
      change
        some
          (TarskiFixedPointUp.mk
            (tarskiFixedPointDecodeBHist (tarskiFixedPointEncodeBHist carrier))
            (tarskiFixedPointDecodeBHist (tarskiFixedPointEncodeBHist order))
            (tarskiFixedPointDecodeBHist (tarskiFixedPointEncodeBHist monotone))
            (tarskiFixedPointDecodeBHist (tarskiFixedPointEncodeBHist prefixRow))
            (tarskiFixedPointDecodeBHist (tarskiFixedPointEncodeBHist postfixRow))
            (tarskiFixedPointDecodeBHist (tarskiFixedPointEncodeBHist iteration))
            (tarskiFixedPointDecodeBHist (tarskiFixedPointEncodeBHist fixed))
            (tarskiFixedPointDecodeBHist (tarskiFixedPointEncodeBHist transport))
            (tarskiFixedPointDecodeBHist (tarskiFixedPointEncodeBHist replay))
            (tarskiFixedPointDecodeBHist (tarskiFixedPointEncodeBHist provenance))
            (tarskiFixedPointDecodeBHist (tarskiFixedPointEncodeBHist localName))) =
          some
            (TarskiFixedPointUp.mk carrier order monotone prefixRow postfixRow iteration fixed
              transport replay provenance localName)
      rw [TarskiFixedPointTasteGate_single_carrier_alignment_decode carrier,
        TarskiFixedPointTasteGate_single_carrier_alignment_decode order,
        TarskiFixedPointTasteGate_single_carrier_alignment_decode monotone,
        TarskiFixedPointTasteGate_single_carrier_alignment_decode prefixRow,
        TarskiFixedPointTasteGate_single_carrier_alignment_decode postfixRow,
        TarskiFixedPointTasteGate_single_carrier_alignment_decode iteration,
        TarskiFixedPointTasteGate_single_carrier_alignment_decode fixed,
        TarskiFixedPointTasteGate_single_carrier_alignment_decode transport,
        TarskiFixedPointTasteGate_single_carrier_alignment_decode replay,
        TarskiFixedPointTasteGate_single_carrier_alignment_decode provenance,
        TarskiFixedPointTasteGate_single_carrier_alignment_decode localName]

private theorem TarskiFixedPointTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : TarskiFixedPointUp} :
    tarskiFixedPointToEventFlow x = tarskiFixedPointToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      tarskiFixedPointFromEventFlow (tarskiFixedPointToEventFlow x) =
        tarskiFixedPointFromEventFlow (tarskiFixedPointToEventFlow y) :=
    congrArg tarskiFixedPointFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (TarskiFixedPointTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (TarskiFixedPointTasteGate_single_carrier_alignment_round_trip y)))

instance tarskiFixedPointBHistCarrier : BHistCarrier TarskiFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := tarskiFixedPointToEventFlow
  fromEventFlow := tarskiFixedPointFromEventFlow

instance tarskiFixedPointChapterTasteGate : ChapterTasteGate TarskiFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change tarskiFixedPointFromEventFlow (tarskiFixedPointToEventFlow x) = some x
    exact TarskiFixedPointTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (TarskiFixedPointTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate TarskiFixedPointUp :=
  -- BEDC touchpoint anchor: BHist BMark
  tarskiFixedPointChapterTasteGate

theorem TarskiFixedPointTasteGate_single_carrier_alignment :
    (∀ h : BHist, tarskiFixedPointDecodeBHist (tarskiFixedPointEncodeBHist h) = h) ∧
      (∀ x : TarskiFixedPointUp,
        tarskiFixedPointFromEventFlow (tarskiFixedPointToEventFlow x) = some x) ∧
        (∀ x y : TarskiFixedPointUp,
          tarskiFixedPointToEventFlow x = tarskiFixedPointToEventFlow y → x = y) ∧
          tarskiFixedPointEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨TarskiFixedPointTasteGate_single_carrier_alignment_decode,
      TarskiFixedPointTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        TarskiFixedPointTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.TarskiFixedPointUp
