import BEDC.Derived.RadonMeasureUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RadonMeasureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def radonMeasureEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: radonMeasureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: radonMeasureEncodeBHist h

def radonMeasureDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (radonMeasureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (radonMeasureDecodeBHist tail)

private theorem RadonMeasureTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, radonMeasureDecodeBHist (radonMeasureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def radonMeasureFields : RadonMeasureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RadonMeasureUp.mk X M O K V D H C P N => [X, M, O, K, V, D, H, C, P, N]

def radonMeasureToEventFlow : RadonMeasureUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (radonMeasureFields x).map radonMeasureEncodeBHist

private def radonMeasureEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => radonMeasureEventAtDefault index rest

def radonMeasureFromEventFlow (ef : EventFlow) : Option RadonMeasureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RadonMeasureUp.mk
      (radonMeasureDecodeBHist (radonMeasureEventAtDefault 0 ef))
      (radonMeasureDecodeBHist (radonMeasureEventAtDefault 1 ef))
      (radonMeasureDecodeBHist (radonMeasureEventAtDefault 2 ef))
      (radonMeasureDecodeBHist (radonMeasureEventAtDefault 3 ef))
      (radonMeasureDecodeBHist (radonMeasureEventAtDefault 4 ef))
      (radonMeasureDecodeBHist (radonMeasureEventAtDefault 5 ef))
      (radonMeasureDecodeBHist (radonMeasureEventAtDefault 6 ef))
      (radonMeasureDecodeBHist (radonMeasureEventAtDefault 7 ef))
      (radonMeasureDecodeBHist (radonMeasureEventAtDefault 8 ef))
      (radonMeasureDecodeBHist (radonMeasureEventAtDefault 9 ef)))

private theorem RadonMeasureTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RadonMeasureUp, radonMeasureFromEventFlow (radonMeasureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk X M O K V D H C P N =>
      change
        some
          (RadonMeasureUp.mk
            (radonMeasureDecodeBHist (radonMeasureEncodeBHist X))
            (radonMeasureDecodeBHist (radonMeasureEncodeBHist M))
            (radonMeasureDecodeBHist (radonMeasureEncodeBHist O))
            (radonMeasureDecodeBHist (radonMeasureEncodeBHist K))
            (radonMeasureDecodeBHist (radonMeasureEncodeBHist V))
            (radonMeasureDecodeBHist (radonMeasureEncodeBHist D))
            (radonMeasureDecodeBHist (radonMeasureEncodeBHist H))
            (radonMeasureDecodeBHist (radonMeasureEncodeBHist C))
            (radonMeasureDecodeBHist (radonMeasureEncodeBHist P))
            (radonMeasureDecodeBHist (radonMeasureEncodeBHist N))) =
          some (RadonMeasureUp.mk X M O K V D H C P N)
      rw [RadonMeasureTasteGate_single_carrier_alignment_decode X,
        RadonMeasureTasteGate_single_carrier_alignment_decode M,
        RadonMeasureTasteGate_single_carrier_alignment_decode O,
        RadonMeasureTasteGate_single_carrier_alignment_decode K,
        RadonMeasureTasteGate_single_carrier_alignment_decode V,
        RadonMeasureTasteGate_single_carrier_alignment_decode D,
        RadonMeasureTasteGate_single_carrier_alignment_decode H,
        RadonMeasureTasteGate_single_carrier_alignment_decode C,
        RadonMeasureTasteGate_single_carrier_alignment_decode P,
        RadonMeasureTasteGate_single_carrier_alignment_decode N]

private theorem RadonMeasureTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RadonMeasureUp} :
    radonMeasureToEventFlow x = radonMeasureToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      radonMeasureFromEventFlow (radonMeasureToEventFlow x) =
        radonMeasureFromEventFlow (radonMeasureToEventFlow y) :=
    congrArg radonMeasureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RadonMeasureTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RadonMeasureTasteGate_single_carrier_alignment_round_trip y)))

private theorem RadonMeasureTasteGate_single_carrier_alignment_fields :
    ∀ x y : RadonMeasureUp, radonMeasureFields x = radonMeasureFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 M1 O1 K1 V1 D1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 M2 O2 K2 V2 D2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance radonMeasureBHistCarrier : BHistCarrier RadonMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := radonMeasureToEventFlow
  fromEventFlow := radonMeasureFromEventFlow

instance radonMeasureChapterTasteGate : ChapterTasteGate RadonMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change radonMeasureFromEventFlow (radonMeasureToEventFlow x) = some x
    exact RadonMeasureTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RadonMeasureTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance radonMeasureFieldFaithful : FieldFaithful RadonMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := radonMeasureFields
  field_faithful := RadonMeasureTasteGate_single_carrier_alignment_fields

instance radonMeasureNontrivial : Nontrivial RadonMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RadonMeasureUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RadonMeasureUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RadonMeasureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  radonMeasureChapterTasteGate

theorem RadonMeasureTasteGate_single_carrier_alignment :
    (∀ h : BHist, radonMeasureDecodeBHist (radonMeasureEncodeBHist h) = h) ∧
      (∀ x : RadonMeasureUp, radonMeasureFromEventFlow (radonMeasureToEventFlow x) = some x) ∧
        (∀ x y : RadonMeasureUp,
          radonMeasureToEventFlow x = radonMeasureToEventFlow y → x = y) ∧
          radonMeasureEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨RadonMeasureTasteGate_single_carrier_alignment_decode,
      RadonMeasureTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RadonMeasureTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RadonMeasureUp
