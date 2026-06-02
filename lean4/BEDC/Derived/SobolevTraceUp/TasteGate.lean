import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SobolevTraceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SobolevTraceUp : Type where
  | mk (S D B R M E H C P N : BHist) : SobolevTraceUp
  deriving DecidableEq

def sobolevTraceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sobolevTraceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sobolevTraceEncodeBHist h

def sobolevTraceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sobolevTraceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sobolevTraceDecodeBHist tail)

private theorem SobolevTraceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, sobolevTraceDecodeBHist (sobolevTraceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sobolevTraceFields : SobolevTraceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SobolevTraceUp.mk S D B R M E H C P N => [S, D, B, R, M, E, H, C, P, N]

def sobolevTraceToEventFlow : SobolevTraceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (sobolevTraceFields x).map sobolevTraceEncodeBHist

private def sobolevTraceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => sobolevTraceEventAtDefault index rest

def sobolevTraceFromEventFlow (ef : EventFlow) : Option SobolevTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SobolevTraceUp.mk
      (sobolevTraceDecodeBHist (sobolevTraceEventAtDefault 0 ef))
      (sobolevTraceDecodeBHist (sobolevTraceEventAtDefault 1 ef))
      (sobolevTraceDecodeBHist (sobolevTraceEventAtDefault 2 ef))
      (sobolevTraceDecodeBHist (sobolevTraceEventAtDefault 3 ef))
      (sobolevTraceDecodeBHist (sobolevTraceEventAtDefault 4 ef))
      (sobolevTraceDecodeBHist (sobolevTraceEventAtDefault 5 ef))
      (sobolevTraceDecodeBHist (sobolevTraceEventAtDefault 6 ef))
      (sobolevTraceDecodeBHist (sobolevTraceEventAtDefault 7 ef))
      (sobolevTraceDecodeBHist (sobolevTraceEventAtDefault 8 ef))
      (sobolevTraceDecodeBHist (sobolevTraceEventAtDefault 9 ef)))

private theorem SobolevTraceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SobolevTraceUp,
      sobolevTraceFromEventFlow (sobolevTraceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S D B R M E H C P N =>
      change
        some
          (SobolevTraceUp.mk
            (sobolevTraceDecodeBHist (sobolevTraceEncodeBHist S))
            (sobolevTraceDecodeBHist (sobolevTraceEncodeBHist D))
            (sobolevTraceDecodeBHist (sobolevTraceEncodeBHist B))
            (sobolevTraceDecodeBHist (sobolevTraceEncodeBHist R))
            (sobolevTraceDecodeBHist (sobolevTraceEncodeBHist M))
            (sobolevTraceDecodeBHist (sobolevTraceEncodeBHist E))
            (sobolevTraceDecodeBHist (sobolevTraceEncodeBHist H))
            (sobolevTraceDecodeBHist (sobolevTraceEncodeBHist C))
            (sobolevTraceDecodeBHist (sobolevTraceEncodeBHist P))
            (sobolevTraceDecodeBHist (sobolevTraceEncodeBHist N))) =
          some (SobolevTraceUp.mk S D B R M E H C P N)
      rw [SobolevTraceTasteGate_single_carrier_alignment_decode S,
        SobolevTraceTasteGate_single_carrier_alignment_decode D,
        SobolevTraceTasteGate_single_carrier_alignment_decode B,
        SobolevTraceTasteGate_single_carrier_alignment_decode R,
        SobolevTraceTasteGate_single_carrier_alignment_decode M,
        SobolevTraceTasteGate_single_carrier_alignment_decode E,
        SobolevTraceTasteGate_single_carrier_alignment_decode H,
        SobolevTraceTasteGate_single_carrier_alignment_decode C,
        SobolevTraceTasteGate_single_carrier_alignment_decode P,
        SobolevTraceTasteGate_single_carrier_alignment_decode N]

private theorem SobolevTraceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SobolevTraceUp} :
    sobolevTraceToEventFlow x = sobolevTraceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sobolevTraceFromEventFlow (sobolevTraceToEventFlow x) =
        sobolevTraceFromEventFlow (sobolevTraceToEventFlow y) :=
    congrArg sobolevTraceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SobolevTraceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SobolevTraceTasteGate_single_carrier_alignment_round_trip y)))

private theorem SobolevTraceTasteGate_single_carrier_alignment_fields :
    ∀ x y : SobolevTraceUp, sobolevTraceFields x = sobolevTraceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 D1 B1 R1 M1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 D2 B2 R2 M2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance sobolevTraceBHistCarrier : BHistCarrier SobolevTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sobolevTraceToEventFlow
  fromEventFlow := sobolevTraceFromEventFlow

instance sobolevTraceChapterTasteGate : ChapterTasteGate SobolevTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sobolevTraceFromEventFlow (sobolevTraceToEventFlow x) = some x
    exact SobolevTraceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SobolevTraceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance sobolevTraceFieldFaithful : FieldFaithful SobolevTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := sobolevTraceFields
  field_faithful := SobolevTraceTasteGate_single_carrier_alignment_fields

instance sobolevTraceNontrivial : Nontrivial SobolevTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SobolevTraceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SobolevTraceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SobolevTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sobolevTraceChapterTasteGate

theorem SobolevTraceTasteGate_single_carrier_alignment :
    (forall h : BHist, sobolevTraceDecodeBHist (sobolevTraceEncodeBHist h) = h) ∧
      (forall x : SobolevTraceUp,
        sobolevTraceFromEventFlow (sobolevTraceToEventFlow x) = some x) ∧
        (forall x y : SobolevTraceUp,
          sobolevTraceToEventFlow x = sobolevTraceToEventFlow y -> x = y) ∧
          sobolevTraceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨SobolevTraceTasteGate_single_carrier_alignment_decode,
      SobolevTraceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => SobolevTraceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SobolevTraceUp
