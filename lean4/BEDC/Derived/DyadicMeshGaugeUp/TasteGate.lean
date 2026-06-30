import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicMeshGaugeUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicMeshGaugeUp : Type where
  | mk (D S W M Q E H C P N : BHist) : DyadicMeshGaugeUp
  deriving DecidableEq

def dyadicMeshGaugeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicMeshGaugeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicMeshGaugeEncodeBHist h

def dyadicMeshGaugeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicMeshGaugeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicMeshGaugeDecodeBHist tail)

private theorem DyadicMeshGaugeTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, dyadicMeshGaugeDecodeBHist (dyadicMeshGaugeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicMeshGaugeFields : DyadicMeshGaugeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicMeshGaugeUp.mk D S W M Q E H C P N => [D, S, W, M, Q, E, H, C, P, N]

def dyadicMeshGaugeToEventFlow : DyadicMeshGaugeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicMeshGaugeFields x).map dyadicMeshGaugeEncodeBHist

private def dyadicMeshGaugeEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicMeshGaugeEventAt index rest

def dyadicMeshGaugeFromEventFlow (ef : EventFlow) : Option DyadicMeshGaugeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicMeshGaugeUp.mk
      (dyadicMeshGaugeDecodeBHist (dyadicMeshGaugeEventAt 0 ef))
      (dyadicMeshGaugeDecodeBHist (dyadicMeshGaugeEventAt 1 ef))
      (dyadicMeshGaugeDecodeBHist (dyadicMeshGaugeEventAt 2 ef))
      (dyadicMeshGaugeDecodeBHist (dyadicMeshGaugeEventAt 3 ef))
      (dyadicMeshGaugeDecodeBHist (dyadicMeshGaugeEventAt 4 ef))
      (dyadicMeshGaugeDecodeBHist (dyadicMeshGaugeEventAt 5 ef))
      (dyadicMeshGaugeDecodeBHist (dyadicMeshGaugeEventAt 6 ef))
      (dyadicMeshGaugeDecodeBHist (dyadicMeshGaugeEventAt 7 ef))
      (dyadicMeshGaugeDecodeBHist (dyadicMeshGaugeEventAt 8 ef))
      (dyadicMeshGaugeDecodeBHist (dyadicMeshGaugeEventAt 9 ef)))

private theorem DyadicMeshGaugeTasteGate_single_carrier_alignment_round_trip
    (x : DyadicMeshGaugeUp) :
    dyadicMeshGaugeFromEventFlow (dyadicMeshGaugeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D S W M Q E H C P N =>
      change
        some
          (DyadicMeshGaugeUp.mk
            (dyadicMeshGaugeDecodeBHist (dyadicMeshGaugeEncodeBHist D))
            (dyadicMeshGaugeDecodeBHist (dyadicMeshGaugeEncodeBHist S))
            (dyadicMeshGaugeDecodeBHist (dyadicMeshGaugeEncodeBHist W))
            (dyadicMeshGaugeDecodeBHist (dyadicMeshGaugeEncodeBHist M))
            (dyadicMeshGaugeDecodeBHist (dyadicMeshGaugeEncodeBHist Q))
            (dyadicMeshGaugeDecodeBHist (dyadicMeshGaugeEncodeBHist E))
            (dyadicMeshGaugeDecodeBHist (dyadicMeshGaugeEncodeBHist H))
            (dyadicMeshGaugeDecodeBHist (dyadicMeshGaugeEncodeBHist C))
            (dyadicMeshGaugeDecodeBHist (dyadicMeshGaugeEncodeBHist P))
            (dyadicMeshGaugeDecodeBHist (dyadicMeshGaugeEncodeBHist N))) =
          some (DyadicMeshGaugeUp.mk D S W M Q E H C P N)
      rw [DyadicMeshGaugeTasteGate_single_carrier_alignment_decode_encode D,
        DyadicMeshGaugeTasteGate_single_carrier_alignment_decode_encode S,
        DyadicMeshGaugeTasteGate_single_carrier_alignment_decode_encode W,
        DyadicMeshGaugeTasteGate_single_carrier_alignment_decode_encode M,
        DyadicMeshGaugeTasteGate_single_carrier_alignment_decode_encode Q,
        DyadicMeshGaugeTasteGate_single_carrier_alignment_decode_encode E,
        DyadicMeshGaugeTasteGate_single_carrier_alignment_decode_encode H,
        DyadicMeshGaugeTasteGate_single_carrier_alignment_decode_encode C,
        DyadicMeshGaugeTasteGate_single_carrier_alignment_decode_encode P,
        DyadicMeshGaugeTasteGate_single_carrier_alignment_decode_encode N]

private theorem DyadicMeshGaugeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicMeshGaugeUp} :
    dyadicMeshGaugeToEventFlow x = dyadicMeshGaugeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicMeshGaugeFromEventFlow (dyadicMeshGaugeToEventFlow x) =
        dyadicMeshGaugeFromEventFlow (dyadicMeshGaugeToEventFlow y) :=
    congrArg dyadicMeshGaugeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DyadicMeshGaugeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DyadicMeshGaugeTasteGate_single_carrier_alignment_round_trip y)))

instance dyadicMeshGaugeBHistCarrier : BHistCarrier DyadicMeshGaugeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicMeshGaugeToEventFlow
  fromEventFlow := dyadicMeshGaugeFromEventFlow

instance dyadicMeshGaugeChapterTasteGate : ChapterTasteGate DyadicMeshGaugeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicMeshGaugeFromEventFlow (dyadicMeshGaugeToEventFlow x) = some x
    exact DyadicMeshGaugeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicMeshGaugeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem DyadicMeshGaugeTasteGate_single_carrier_alignment :
    (∃ carrier : BHistCarrier DyadicMeshGaugeUp,
        Nonempty (@ChapterTasteGate DyadicMeshGaugeUp carrier)) ∧
      (∀ h : BHist, dyadicMeshGaugeDecodeBHist (dyadicMeshGaugeEncodeBHist h) = h) ∧
        (∀ x : DyadicMeshGaugeUp,
          dyadicMeshGaugeFromEventFlow (dyadicMeshGaugeToEventFlow x) = some x) ∧
          dyadicMeshGaugeEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨dyadicMeshGaugeBHistCarrier, ⟨dyadicMeshGaugeChapterTasteGate⟩⟩,
      DyadicMeshGaugeTasteGate_single_carrier_alignment_decode_encode,
      DyadicMeshGaugeTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.DyadicMeshGaugeUp.TasteGate
