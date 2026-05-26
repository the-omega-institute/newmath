import BEDC.Derived.SeparatedQuotientMetricUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SeparatedQuotientMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def separatedQuotientMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: separatedQuotientMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: separatedQuotientMetricEncodeBHist h

def separatedQuotientMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (separatedQuotientMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (separatedQuotientMetricDecodeBHist tail)

private theorem SeparatedQuotientMetricTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, separatedQuotientMetricDecodeBHist
      (separatedQuotientMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def separatedQuotientMetricFields : SeparatedQuotientMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SeparatedQuotientMetricUp.mk X P Z S R E H C N => [X, P, Z, S, R, E, H, C, N]

def separatedQuotientMetricToEventFlow : SeparatedQuotientMetricUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (separatedQuotientMetricFields x).map separatedQuotientMetricEncodeBHist

private def separatedQuotientMetricEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => separatedQuotientMetricEventAtDefault index rest

def separatedQuotientMetricFromEventFlow (ef : EventFlow) :
    Option SeparatedQuotientMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SeparatedQuotientMetricUp.mk
      (separatedQuotientMetricDecodeBHist (separatedQuotientMetricEventAtDefault 0 ef))
      (separatedQuotientMetricDecodeBHist (separatedQuotientMetricEventAtDefault 1 ef))
      (separatedQuotientMetricDecodeBHist (separatedQuotientMetricEventAtDefault 2 ef))
      (separatedQuotientMetricDecodeBHist (separatedQuotientMetricEventAtDefault 3 ef))
      (separatedQuotientMetricDecodeBHist (separatedQuotientMetricEventAtDefault 4 ef))
      (separatedQuotientMetricDecodeBHist (separatedQuotientMetricEventAtDefault 5 ef))
      (separatedQuotientMetricDecodeBHist (separatedQuotientMetricEventAtDefault 6 ef))
      (separatedQuotientMetricDecodeBHist (separatedQuotientMetricEventAtDefault 7 ef))
      (separatedQuotientMetricDecodeBHist (separatedQuotientMetricEventAtDefault 8 ef)))

private theorem SeparatedQuotientMetricTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SeparatedQuotientMetricUp,
      separatedQuotientMetricFromEventFlow
        (separatedQuotientMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk X P Z S R E H C N =>
      change
        some
          (SeparatedQuotientMetricUp.mk
            (separatedQuotientMetricDecodeBHist (separatedQuotientMetricEncodeBHist X))
            (separatedQuotientMetricDecodeBHist (separatedQuotientMetricEncodeBHist P))
            (separatedQuotientMetricDecodeBHist (separatedQuotientMetricEncodeBHist Z))
            (separatedQuotientMetricDecodeBHist (separatedQuotientMetricEncodeBHist S))
            (separatedQuotientMetricDecodeBHist (separatedQuotientMetricEncodeBHist R))
            (separatedQuotientMetricDecodeBHist (separatedQuotientMetricEncodeBHist E))
            (separatedQuotientMetricDecodeBHist (separatedQuotientMetricEncodeBHist H))
            (separatedQuotientMetricDecodeBHist (separatedQuotientMetricEncodeBHist C))
            (separatedQuotientMetricDecodeBHist (separatedQuotientMetricEncodeBHist N))) =
          some (SeparatedQuotientMetricUp.mk X P Z S R E H C N)
      rw [SeparatedQuotientMetricTasteGate_single_carrier_alignment_decode X,
        SeparatedQuotientMetricTasteGate_single_carrier_alignment_decode P,
        SeparatedQuotientMetricTasteGate_single_carrier_alignment_decode Z,
        SeparatedQuotientMetricTasteGate_single_carrier_alignment_decode S,
        SeparatedQuotientMetricTasteGate_single_carrier_alignment_decode R,
        SeparatedQuotientMetricTasteGate_single_carrier_alignment_decode E,
        SeparatedQuotientMetricTasteGate_single_carrier_alignment_decode H,
        SeparatedQuotientMetricTasteGate_single_carrier_alignment_decode C,
        SeparatedQuotientMetricTasteGate_single_carrier_alignment_decode N]

private theorem SeparatedQuotientMetricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SeparatedQuotientMetricUp} :
    separatedQuotientMetricToEventFlow x = separatedQuotientMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      separatedQuotientMetricFromEventFlow (separatedQuotientMetricToEventFlow x) =
        separatedQuotientMetricFromEventFlow (separatedQuotientMetricToEventFlow y) :=
    congrArg separatedQuotientMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SeparatedQuotientMetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SeparatedQuotientMetricTasteGate_single_carrier_alignment_round_trip y)))

private theorem SeparatedQuotientMetricTasteGate_single_carrier_alignment_fields :
    ∀ x y : SeparatedQuotientMetricUp, separatedQuotientMetricFields x =
      separatedQuotientMetricFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 P1 Z1 S1 R1 E1 H1 C1 N1 =>
      cases y with
      | mk X2 P2 Z2 S2 R2 E2 H2 C2 N2 =>
          cases hfields
          rfl

instance separatedQuotientMetricBHistCarrier :
    BHistCarrier SeparatedQuotientMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := separatedQuotientMetricToEventFlow
  fromEventFlow := separatedQuotientMetricFromEventFlow

instance separatedQuotientMetricChapterTasteGate :
    ChapterTasteGate SeparatedQuotientMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change separatedQuotientMetricFromEventFlow (separatedQuotientMetricToEventFlow x) = some x
    exact SeparatedQuotientMetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SeparatedQuotientMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance separatedQuotientMetricFieldFaithful :
    FieldFaithful SeparatedQuotientMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := separatedQuotientMetricFields
  field_faithful := SeparatedQuotientMetricTasteGate_single_carrier_alignment_fields

instance separatedQuotientMetricNontrivial : Nontrivial SeparatedQuotientMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SeparatedQuotientMetricUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SeparatedQuotientMetricUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SeparatedQuotientMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  separatedQuotientMetricChapterTasteGate

theorem SeparatedQuotientMetricTasteGate_single_carrier_alignment :
    (∀ h : BHist, separatedQuotientMetricDecodeBHist
        (separatedQuotientMetricEncodeBHist h) = h) ∧
      (∀ x : SeparatedQuotientMetricUp,
        separatedQuotientMetricFromEventFlow (separatedQuotientMetricToEventFlow x) = some x) ∧
        (∀ x y : SeparatedQuotientMetricUp,
          separatedQuotientMetricToEventFlow x = separatedQuotientMetricToEventFlow y → x = y) ∧
          separatedQuotientMetricEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨SeparatedQuotientMetricTasteGate_single_carrier_alignment_decode,
      SeparatedQuotientMetricTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        SeparatedQuotientMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SeparatedQuotientMetricUp
