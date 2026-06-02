import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyNetRegularizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyNetRegularizationUp : Type where
  | mk (D S R T A E M H C P N : BHist) : CauchyNetRegularizationUp
  deriving DecidableEq

def cauchyNetRegularizationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyNetRegularizationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyNetRegularizationEncodeBHist h

def cauchyNetRegularizationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyNetRegularizationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyNetRegularizationDecodeBHist tail)

private theorem CauchyNetRegularizationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyNetRegularizationDecodeBHist (cauchyNetRegularizationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyNetRegularizationFields : CauchyNetRegularizationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyNetRegularizationUp.mk D S R T A E M H C P N =>
      [D, S, R, T, A, E, M, H, C, P, N]

def cauchyNetRegularizationToEventFlow : CauchyNetRegularizationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchyNetRegularizationFields x).map cauchyNetRegularizationEncodeBHist

private def cauchyNetRegularizationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyNetRegularizationEventAtDefault index rest

def cauchyNetRegularizationFromEventFlow
    (ef : EventFlow) : Option CauchyNetRegularizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyNetRegularizationUp.mk
      (cauchyNetRegularizationDecodeBHist (cauchyNetRegularizationEventAtDefault 0 ef))
      (cauchyNetRegularizationDecodeBHist (cauchyNetRegularizationEventAtDefault 1 ef))
      (cauchyNetRegularizationDecodeBHist (cauchyNetRegularizationEventAtDefault 2 ef))
      (cauchyNetRegularizationDecodeBHist (cauchyNetRegularizationEventAtDefault 3 ef))
      (cauchyNetRegularizationDecodeBHist (cauchyNetRegularizationEventAtDefault 4 ef))
      (cauchyNetRegularizationDecodeBHist (cauchyNetRegularizationEventAtDefault 5 ef))
      (cauchyNetRegularizationDecodeBHist (cauchyNetRegularizationEventAtDefault 6 ef))
      (cauchyNetRegularizationDecodeBHist (cauchyNetRegularizationEventAtDefault 7 ef))
      (cauchyNetRegularizationDecodeBHist (cauchyNetRegularizationEventAtDefault 8 ef))
      (cauchyNetRegularizationDecodeBHist (cauchyNetRegularizationEventAtDefault 9 ef))
      (cauchyNetRegularizationDecodeBHist (cauchyNetRegularizationEventAtDefault 10 ef)))

private theorem CauchyNetRegularizationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyNetRegularizationUp,
      cauchyNetRegularizationFromEventFlow (cauchyNetRegularizationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R T A E M H C P N =>
      change
        some
          (CauchyNetRegularizationUp.mk
            (cauchyNetRegularizationDecodeBHist (cauchyNetRegularizationEncodeBHist D))
            (cauchyNetRegularizationDecodeBHist (cauchyNetRegularizationEncodeBHist S))
            (cauchyNetRegularizationDecodeBHist (cauchyNetRegularizationEncodeBHist R))
            (cauchyNetRegularizationDecodeBHist (cauchyNetRegularizationEncodeBHist T))
            (cauchyNetRegularizationDecodeBHist (cauchyNetRegularizationEncodeBHist A))
            (cauchyNetRegularizationDecodeBHist (cauchyNetRegularizationEncodeBHist E))
            (cauchyNetRegularizationDecodeBHist (cauchyNetRegularizationEncodeBHist M))
            (cauchyNetRegularizationDecodeBHist (cauchyNetRegularizationEncodeBHist H))
            (cauchyNetRegularizationDecodeBHist (cauchyNetRegularizationEncodeBHist C))
            (cauchyNetRegularizationDecodeBHist (cauchyNetRegularizationEncodeBHist P))
            (cauchyNetRegularizationDecodeBHist (cauchyNetRegularizationEncodeBHist N))) =
          some (CauchyNetRegularizationUp.mk D S R T A E M H C P N)
      rw [CauchyNetRegularizationTasteGate_single_carrier_alignment_decode D,
        CauchyNetRegularizationTasteGate_single_carrier_alignment_decode S,
        CauchyNetRegularizationTasteGate_single_carrier_alignment_decode R,
        CauchyNetRegularizationTasteGate_single_carrier_alignment_decode T,
        CauchyNetRegularizationTasteGate_single_carrier_alignment_decode A,
        CauchyNetRegularizationTasteGate_single_carrier_alignment_decode E,
        CauchyNetRegularizationTasteGate_single_carrier_alignment_decode M,
        CauchyNetRegularizationTasteGate_single_carrier_alignment_decode H,
        CauchyNetRegularizationTasteGate_single_carrier_alignment_decode C,
        CauchyNetRegularizationTasteGate_single_carrier_alignment_decode P,
        CauchyNetRegularizationTasteGate_single_carrier_alignment_decode N]

private theorem CauchyNetRegularizationTasteGate_single_carrier_alignment_injective
    {x y : CauchyNetRegularizationUp} :
    cauchyNetRegularizationToEventFlow x = cauchyNetRegularizationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyNetRegularizationFromEventFlow (cauchyNetRegularizationToEventFlow x) =
        cauchyNetRegularizationFromEventFlow (cauchyNetRegularizationToEventFlow y) :=
    congrArg cauchyNetRegularizationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyNetRegularizationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyNetRegularizationTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyNetRegularizationTasteGate_single_carrier_alignment_fields :
    ∀ x y : CauchyNetRegularizationUp,
      cauchyNetRegularizationFields x = cauchyNetRegularizationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D1 S1 R1 T1 A1 E1 M1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 S2 R2 T2 A2 E2 M2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchyNetRegularizationBHistCarrier : BHistCarrier CauchyNetRegularizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyNetRegularizationToEventFlow
  fromEventFlow := cauchyNetRegularizationFromEventFlow

instance cauchyNetRegularizationChapterTasteGate : ChapterTasteGate CauchyNetRegularizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyNetRegularizationFromEventFlow (cauchyNetRegularizationToEventFlow x) = some x
    exact CauchyNetRegularizationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyNetRegularizationTasteGate_single_carrier_alignment_injective heq)

instance cauchyNetRegularizationFieldFaithful : FieldFaithful CauchyNetRegularizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyNetRegularizationFields
  field_faithful := CauchyNetRegularizationTasteGate_single_carrier_alignment_fields

instance cauchyNetRegularizationNontrivial : Nontrivial CauchyNetRegularizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyNetRegularizationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CauchyNetRegularizationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyNetRegularizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyNetRegularizationChapterTasteGate

theorem CauchyNetRegularizationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyNetRegularizationDecodeBHist (cauchyNetRegularizationEncodeBHist h) = h) ∧
      (∀ x : CauchyNetRegularizationUp,
        cauchyNetRegularizationFromEventFlow (cauchyNetRegularizationToEventFlow x) =
          some x) ∧
        (∀ x y : CauchyNetRegularizationUp,
          cauchyNetRegularizationToEventFlow x = cauchyNetRegularizationToEventFlow y →
            x = y) ∧
          cauchyNetRegularizationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨CauchyNetRegularizationTasteGate_single_carrier_alignment_decode,
      CauchyNetRegularizationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CauchyNetRegularizationTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.CauchyNetRegularizationUp
