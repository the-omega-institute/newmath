import BEDC.Derived.CauchyRateRealizationUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRateRealizationUp

open BEDC.Derived
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def cauchyRateRealizationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyRateRealizationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyRateRealizationEncodeBHist h

def cauchyRateRealizationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyRateRealizationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyRateRealizationDecodeBHist tail)

private theorem CauchyRateRealizationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, cauchyRateRealizationDecodeBHist (cauchyRateRealizationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyRateRealizationFields : CauchyRateRealizationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRateRealizationUp.mk p r d s q m e H C P N => [p, r, d, s, q, m, e, H, C, P, N]

def cauchyRateRealizationToEventFlow : CauchyRateRealizationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchyRateRealizationFields x).map cauchyRateRealizationEncodeBHist

private def cauchyRateRealizationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyRateRealizationEventAtDefault index rest

def cauchyRateRealizationFromEventFlow (ef : EventFlow) : Option CauchyRateRealizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyRateRealizationUp.mk
      (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEventAtDefault 0 ef))
      (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEventAtDefault 1 ef))
      (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEventAtDefault 2 ef))
      (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEventAtDefault 3 ef))
      (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEventAtDefault 4 ef))
      (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEventAtDefault 5 ef))
      (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEventAtDefault 6 ef))
      (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEventAtDefault 7 ef))
      (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEventAtDefault 8 ef))
      (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEventAtDefault 9 ef))
      (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEventAtDefault 10 ef)))

private theorem CauchyRateRealizationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyRateRealizationUp,
      cauchyRateRealizationFromEventFlow (cauchyRateRealizationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk p r d s q m e H C P N =>
      change
        some
          (CauchyRateRealizationUp.mk
            (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEncodeBHist p))
            (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEncodeBHist r))
            (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEncodeBHist d))
            (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEncodeBHist s))
            (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEncodeBHist q))
            (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEncodeBHist m))
            (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEncodeBHist e))
            (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEncodeBHist H))
            (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEncodeBHist C))
            (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEncodeBHist P))
            (cauchyRateRealizationDecodeBHist (cauchyRateRealizationEncodeBHist N))) =
          some (CauchyRateRealizationUp.mk p r d s q m e H C P N)
      rw [CauchyRateRealizationTasteGate_single_carrier_alignment_decode p,
        CauchyRateRealizationTasteGate_single_carrier_alignment_decode r,
        CauchyRateRealizationTasteGate_single_carrier_alignment_decode d,
        CauchyRateRealizationTasteGate_single_carrier_alignment_decode s,
        CauchyRateRealizationTasteGate_single_carrier_alignment_decode q,
        CauchyRateRealizationTasteGate_single_carrier_alignment_decode m,
        CauchyRateRealizationTasteGate_single_carrier_alignment_decode e,
        CauchyRateRealizationTasteGate_single_carrier_alignment_decode H,
        CauchyRateRealizationTasteGate_single_carrier_alignment_decode C,
        CauchyRateRealizationTasteGate_single_carrier_alignment_decode P,
        CauchyRateRealizationTasteGate_single_carrier_alignment_decode N]

private theorem CauchyRateRealizationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyRateRealizationUp} :
    cauchyRateRealizationToEventFlow x = cauchyRateRealizationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRateRealizationFromEventFlow (cauchyRateRealizationToEventFlow x) =
        cauchyRateRealizationFromEventFlow (cauchyRateRealizationToEventFlow y) :=
    congrArg cauchyRateRealizationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyRateRealizationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyRateRealizationTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyRateRealizationTasteGate_single_carrier_alignment_fields :
    ∀ x y : CauchyRateRealizationUp,
      cauchyRateRealizationFields x = cauchyRateRealizationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk p1 r1 d1 s1 q1 m1 e1 H1 C1 P1 N1 =>
      cases y with
      | mk p2 r2 d2 s2 q2 m2 e2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchyRateRealizationBHistCarrier : BHistCarrier CauchyRateRealizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyRateRealizationToEventFlow
  fromEventFlow := cauchyRateRealizationFromEventFlow

instance cauchyRateRealizationChapterTasteGate : ChapterTasteGate CauchyRateRealizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyRateRealizationFromEventFlow (cauchyRateRealizationToEventFlow x) = some x
    exact CauchyRateRealizationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyRateRealizationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyRateRealizationFieldFaithful : FieldFaithful CauchyRateRealizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyRateRealizationFields
  field_faithful := CauchyRateRealizationTasteGate_single_carrier_alignment_fields

instance cauchyRateRealizationNontrivial : Nontrivial CauchyRateRealizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyRateRealizationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyRateRealizationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyRateRealizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyRateRealizationChapterTasteGate

theorem CauchyRateRealizationTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyRateRealizationDecodeBHist (cauchyRateRealizationEncodeBHist h) = h) ∧
      (∀ x : CauchyRateRealizationUp,
        cauchyRateRealizationFromEventFlow (cauchyRateRealizationToEventFlow x) = some x) ∧
      (∀ x y : CauchyRateRealizationUp,
        cauchyRateRealizationToEventFlow x = cauchyRateRealizationToEventFlow y → x = y) ∧
      cauchyRateRealizationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨CauchyRateRealizationTasteGate_single_carrier_alignment_decode,
      CauchyRateRealizationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyRateRealizationTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyRateRealizationUp
