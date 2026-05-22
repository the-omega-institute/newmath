import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyMajorantSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyMajorantSeriesUp : Type where
  | mk (A D S R B E H C P N : BHist) : CauchyMajorantSeriesUp
  deriving DecidableEq

def cauchyMajorantSeriesEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyMajorantSeriesEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyMajorantSeriesEncodeBHist h

def cauchyMajorantSeriesDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyMajorantSeriesDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyMajorantSeriesDecodeBHist tail)

private theorem CauchyMajorantSeriesTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyMajorantSeriesFields : CauchyMajorantSeriesUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyMajorantSeriesUp.mk A D S R B E H C P N => [A, D, S, R, B, E, H, C, P, N]

def cauchyMajorantSeriesToEventFlow : CauchyMajorantSeriesUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyMajorantSeriesFields x).map cauchyMajorantSeriesEncodeBHist

private def cauchyMajorantSeriesRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyMajorantSeriesRawAt index rest

def cauchyMajorantSeriesFromEventFlow
    (flow : EventFlow) : Option CauchyMajorantSeriesUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyMajorantSeriesUp.mk
      (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesRawAt 0 flow))
      (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesRawAt 1 flow))
      (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesRawAt 2 flow))
      (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesRawAt 3 flow))
      (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesRawAt 4 flow))
      (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesRawAt 5 flow))
      (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesRawAt 6 flow))
      (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesRawAt 7 flow))
      (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesRawAt 8 flow))
      (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesRawAt 9 flow)))

private theorem CauchyMajorantSeriesTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyMajorantSeriesUp,
      cauchyMajorantSeriesFromEventFlow (cauchyMajorantSeriesToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A D S R B E H C P N =>
      change
        some
          (CauchyMajorantSeriesUp.mk
            (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEncodeBHist A))
            (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEncodeBHist D))
            (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEncodeBHist S))
            (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEncodeBHist R))
            (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEncodeBHist B))
            (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEncodeBHist E))
            (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEncodeBHist H))
            (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEncodeBHist C))
            (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEncodeBHist P))
            (cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEncodeBHist N))) =
          some (CauchyMajorantSeriesUp.mk A D S R B E H C P N)
      rw [CauchyMajorantSeriesTasteGate_single_carrier_alignment_decode_encode A,
        CauchyMajorantSeriesTasteGate_single_carrier_alignment_decode_encode D,
        CauchyMajorantSeriesTasteGate_single_carrier_alignment_decode_encode S,
        CauchyMajorantSeriesTasteGate_single_carrier_alignment_decode_encode R,
        CauchyMajorantSeriesTasteGate_single_carrier_alignment_decode_encode B,
        CauchyMajorantSeriesTasteGate_single_carrier_alignment_decode_encode E,
        CauchyMajorantSeriesTasteGate_single_carrier_alignment_decode_encode H,
        CauchyMajorantSeriesTasteGate_single_carrier_alignment_decode_encode C,
        CauchyMajorantSeriesTasteGate_single_carrier_alignment_decode_encode P,
        CauchyMajorantSeriesTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyMajorantSeriesTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyMajorantSeriesUp} :
    cauchyMajorantSeriesToEventFlow x = cauchyMajorantSeriesToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyMajorantSeriesFromEventFlow (cauchyMajorantSeriesToEventFlow x) =
        cauchyMajorantSeriesFromEventFlow (cauchyMajorantSeriesToEventFlow y) :=
    congrArg cauchyMajorantSeriesFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyMajorantSeriesTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyMajorantSeriesTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyMajorantSeriesTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CauchyMajorantSeriesUp,
      cauchyMajorantSeriesFields x = cauchyMajorantSeriesFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk A1 D1 S1 R1 B1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk A2 D2 S2 R2 B2 E2 H2 C2 P2 N2 =>
          simp only [cauchyMajorantSeriesFields] at h
          cases h
          rfl

instance cauchyMajorantSeriesBHistCarrier : BHistCarrier CauchyMajorantSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyMajorantSeriesToEventFlow
  fromEventFlow := cauchyMajorantSeriesFromEventFlow

instance cauchyMajorantSeriesChapterTasteGate :
    ChapterTasteGate CauchyMajorantSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyMajorantSeriesFromEventFlow (cauchyMajorantSeriesToEventFlow x) = some x
    exact CauchyMajorantSeriesTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyMajorantSeriesTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyMajorantSeriesFieldFaithful : FieldFaithful CauchyMajorantSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyMajorantSeriesFields
  field_faithful := CauchyMajorantSeriesTasteGate_single_carrier_alignment_fields_faithful

instance cauchyMajorantSeriesNontrivial : Nontrivial CauchyMajorantSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyMajorantSeriesUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyMajorantSeriesUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CauchyMajorantSeriesTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyMajorantSeriesDecodeBHist (cauchyMajorantSeriesEncodeBHist h) = h) ∧
      (∀ x : CauchyMajorantSeriesUp,
        cauchyMajorantSeriesFromEventFlow (cauchyMajorantSeriesToEventFlow x) =
          some x) ∧
        (∀ x y : CauchyMajorantSeriesUp,
          cauchyMajorantSeriesToEventFlow x = cauchyMajorantSeriesToEventFlow y →
            x = y) ∧
          cauchyMajorantSeriesEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨CauchyMajorantSeriesTasteGate_single_carrier_alignment_decode_encode,
      CauchyMajorantSeriesTasteGate_single_carrier_alignment_round_trip,
      by
        intro x y heq
        exact CauchyMajorantSeriesTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.CauchyMajorantSeriesUp
