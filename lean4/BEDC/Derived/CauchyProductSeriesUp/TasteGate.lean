import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyProductSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyProductSeriesUp : Type where
  | mk (L R W C D F Q E H T P N : BHist) : CauchyProductSeriesUp
  deriving DecidableEq

def cauchyProductSeriesEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyProductSeriesEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyProductSeriesEncodeBHist h

def cauchyProductSeriesDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyProductSeriesDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyProductSeriesDecodeBHist tail)

private theorem CauchyProductSeriesTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchyProductSeriesDecodeBHist (cauchyProductSeriesEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyProductSeriesToEventFlow : CauchyProductSeriesUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyProductSeriesUp.mk L R W C D F Q E H T P N =>
      [cauchyProductSeriesEncodeBHist L,
        cauchyProductSeriesEncodeBHist R,
        cauchyProductSeriesEncodeBHist W,
        cauchyProductSeriesEncodeBHist C,
        cauchyProductSeriesEncodeBHist D,
        cauchyProductSeriesEncodeBHist F,
        cauchyProductSeriesEncodeBHist Q,
        cauchyProductSeriesEncodeBHist E,
        cauchyProductSeriesEncodeBHist H,
        cauchyProductSeriesEncodeBHist T,
        cauchyProductSeriesEncodeBHist P,
        cauchyProductSeriesEncodeBHist N]

private def cauchyProductSeriesEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyProductSeriesEventAtDefault index rest

def cauchyProductSeriesFromEventFlow (ef : EventFlow) : Option CauchyProductSeriesUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyProductSeriesUp.mk
      (cauchyProductSeriesDecodeBHist (cauchyProductSeriesEventAtDefault 0 ef))
      (cauchyProductSeriesDecodeBHist (cauchyProductSeriesEventAtDefault 1 ef))
      (cauchyProductSeriesDecodeBHist (cauchyProductSeriesEventAtDefault 2 ef))
      (cauchyProductSeriesDecodeBHist (cauchyProductSeriesEventAtDefault 3 ef))
      (cauchyProductSeriesDecodeBHist (cauchyProductSeriesEventAtDefault 4 ef))
      (cauchyProductSeriesDecodeBHist (cauchyProductSeriesEventAtDefault 5 ef))
      (cauchyProductSeriesDecodeBHist (cauchyProductSeriesEventAtDefault 6 ef))
      (cauchyProductSeriesDecodeBHist (cauchyProductSeriesEventAtDefault 7 ef))
      (cauchyProductSeriesDecodeBHist (cauchyProductSeriesEventAtDefault 8 ef))
      (cauchyProductSeriesDecodeBHist (cauchyProductSeriesEventAtDefault 9 ef))
      (cauchyProductSeriesDecodeBHist (cauchyProductSeriesEventAtDefault 10 ef))
      (cauchyProductSeriesDecodeBHist (cauchyProductSeriesEventAtDefault 11 ef)))

private theorem CauchyProductSeriesTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyProductSeriesUp,
      cauchyProductSeriesFromEventFlow (cauchyProductSeriesToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L R W C D F Q E H T P N =>
      change
        some
          (CauchyProductSeriesUp.mk
            (cauchyProductSeriesDecodeBHist (cauchyProductSeriesEncodeBHist L))
            (cauchyProductSeriesDecodeBHist (cauchyProductSeriesEncodeBHist R))
            (cauchyProductSeriesDecodeBHist (cauchyProductSeriesEncodeBHist W))
            (cauchyProductSeriesDecodeBHist (cauchyProductSeriesEncodeBHist C))
            (cauchyProductSeriesDecodeBHist (cauchyProductSeriesEncodeBHist D))
            (cauchyProductSeriesDecodeBHist (cauchyProductSeriesEncodeBHist F))
            (cauchyProductSeriesDecodeBHist (cauchyProductSeriesEncodeBHist Q))
            (cauchyProductSeriesDecodeBHist (cauchyProductSeriesEncodeBHist E))
            (cauchyProductSeriesDecodeBHist (cauchyProductSeriesEncodeBHist H))
            (cauchyProductSeriesDecodeBHist (cauchyProductSeriesEncodeBHist T))
            (cauchyProductSeriesDecodeBHist (cauchyProductSeriesEncodeBHist P))
            (cauchyProductSeriesDecodeBHist (cauchyProductSeriesEncodeBHist N))) =
          some (CauchyProductSeriesUp.mk L R W C D F Q E H T P N)
      rw [CauchyProductSeriesTasteGate_single_carrier_alignment_decode_encode L,
        CauchyProductSeriesTasteGate_single_carrier_alignment_decode_encode R,
        CauchyProductSeriesTasteGate_single_carrier_alignment_decode_encode W,
        CauchyProductSeriesTasteGate_single_carrier_alignment_decode_encode C,
        CauchyProductSeriesTasteGate_single_carrier_alignment_decode_encode D,
        CauchyProductSeriesTasteGate_single_carrier_alignment_decode_encode F,
        CauchyProductSeriesTasteGate_single_carrier_alignment_decode_encode Q,
        CauchyProductSeriesTasteGate_single_carrier_alignment_decode_encode E,
        CauchyProductSeriesTasteGate_single_carrier_alignment_decode_encode H,
        CauchyProductSeriesTasteGate_single_carrier_alignment_decode_encode T,
        CauchyProductSeriesTasteGate_single_carrier_alignment_decode_encode P,
        CauchyProductSeriesTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyProductSeriesTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyProductSeriesUp} :
    cauchyProductSeriesToEventFlow x = cauchyProductSeriesToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyProductSeriesFromEventFlow (cauchyProductSeriesToEventFlow x) =
        cauchyProductSeriesFromEventFlow (cauchyProductSeriesToEventFlow y) :=
    congrArg cauchyProductSeriesFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyProductSeriesTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyProductSeriesTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyProductSeriesBHistCarrier : BHistCarrier CauchyProductSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyProductSeriesToEventFlow
  fromEventFlow := cauchyProductSeriesFromEventFlow

instance cauchyProductSeriesChapterTasteGate : ChapterTasteGate CauchyProductSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyProductSeriesFromEventFlow (cauchyProductSeriesToEventFlow x) = some x
    exact CauchyProductSeriesTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyProductSeriesTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyProductSeriesFieldFaithful : FieldFaithful CauchyProductSeriesUp where
  fields := fun x =>
    match x with
    | CauchyProductSeriesUp.mk L R W C D F Q E H T P N => [L, R, W, C, D, F, Q, E, H, T, P, N]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk L1 R1 W1 C1 D1 F1 Q1 E1 H1 T1 P1 N1 =>
      cases y with
      | mk L2 R2 W2 C2 D2 F2 Q2 E2 H2 T2 P2 N2 =>
        cases h
        rfl

instance cauchyProductSeriesNontrivial : Nontrivial CauchyProductSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyProductSeriesUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyProductSeriesUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def cauchyProductSeriesTasteGate : ChapterTasteGate CauchyProductSeriesUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyProductSeriesChapterTasteGate

theorem CauchyProductSeriesTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyProductSeriesDecodeBHist (cauchyProductSeriesEncodeBHist h) = h) ∧
      (∀ x : CauchyProductSeriesUp,
        cauchyProductSeriesFromEventFlow (cauchyProductSeriesToEventFlow x) = some x) ∧
        (∀ x y : CauchyProductSeriesUp,
          cauchyProductSeriesToEventFlow x = cauchyProductSeriesToEventFlow y → x = y) ∧
          cauchyProductSeriesEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyProductSeriesTasteGate_single_carrier_alignment_decode_encode,
      CauchyProductSeriesTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CauchyProductSeriesTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyProductSeriesUp
