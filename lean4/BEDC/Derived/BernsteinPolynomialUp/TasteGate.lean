import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BernsteinPolynomialUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BernsteinPolynomialUp : Type where
  | mk (I F U M S K E H C P N : BHist) : BernsteinPolynomialUp
  deriving DecidableEq

def bernsteinPolynomialEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bernsteinPolynomialEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bernsteinPolynomialEncodeBHist h

def bernsteinPolynomialDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bernsteinPolynomialDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bernsteinPolynomialDecodeBHist tail)

private theorem BernsteinPolynomialTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bernsteinPolynomialDecodeBHist (bernsteinPolynomialEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bernsteinPolynomialFields : BernsteinPolynomialUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BernsteinPolynomialUp.mk I F U M S K E H C P N => [I, F, U, M, S, K, E, H, C, P, N]

def bernsteinPolynomialToEventFlow : BernsteinPolynomialUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map bernsteinPolynomialEncodeBHist (bernsteinPolynomialFields x)

private def bernsteinPolynomialEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bernsteinPolynomialEventAtDefault index rest

def bernsteinPolynomialFromEventFlow (ef : EventFlow) : Option BernsteinPolynomialUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BernsteinPolynomialUp.mk
      (bernsteinPolynomialDecodeBHist (bernsteinPolynomialEventAtDefault 0 ef))
      (bernsteinPolynomialDecodeBHist (bernsteinPolynomialEventAtDefault 1 ef))
      (bernsteinPolynomialDecodeBHist (bernsteinPolynomialEventAtDefault 2 ef))
      (bernsteinPolynomialDecodeBHist (bernsteinPolynomialEventAtDefault 3 ef))
      (bernsteinPolynomialDecodeBHist (bernsteinPolynomialEventAtDefault 4 ef))
      (bernsteinPolynomialDecodeBHist (bernsteinPolynomialEventAtDefault 5 ef))
      (bernsteinPolynomialDecodeBHist (bernsteinPolynomialEventAtDefault 6 ef))
      (bernsteinPolynomialDecodeBHist (bernsteinPolynomialEventAtDefault 7 ef))
      (bernsteinPolynomialDecodeBHist (bernsteinPolynomialEventAtDefault 8 ef))
      (bernsteinPolynomialDecodeBHist (bernsteinPolynomialEventAtDefault 9 ef))
      (bernsteinPolynomialDecodeBHist (bernsteinPolynomialEventAtDefault 10 ef)))

private theorem BernsteinPolynomialTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BernsteinPolynomialUp,
      bernsteinPolynomialFromEventFlow (bernsteinPolynomialToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I F U M S K E H C P N =>
      change
        some
          (BernsteinPolynomialUp.mk
            (bernsteinPolynomialDecodeBHist (bernsteinPolynomialEncodeBHist I))
            (bernsteinPolynomialDecodeBHist (bernsteinPolynomialEncodeBHist F))
            (bernsteinPolynomialDecodeBHist (bernsteinPolynomialEncodeBHist U))
            (bernsteinPolynomialDecodeBHist (bernsteinPolynomialEncodeBHist M))
            (bernsteinPolynomialDecodeBHist (bernsteinPolynomialEncodeBHist S))
            (bernsteinPolynomialDecodeBHist (bernsteinPolynomialEncodeBHist K))
            (bernsteinPolynomialDecodeBHist (bernsteinPolynomialEncodeBHist E))
            (bernsteinPolynomialDecodeBHist (bernsteinPolynomialEncodeBHist H))
            (bernsteinPolynomialDecodeBHist (bernsteinPolynomialEncodeBHist C))
            (bernsteinPolynomialDecodeBHist (bernsteinPolynomialEncodeBHist P))
            (bernsteinPolynomialDecodeBHist (bernsteinPolynomialEncodeBHist N))) =
          some (BernsteinPolynomialUp.mk I F U M S K E H C P N)
      rw [BernsteinPolynomialTasteGate_single_carrier_alignment_decode I,
        BernsteinPolynomialTasteGate_single_carrier_alignment_decode F,
        BernsteinPolynomialTasteGate_single_carrier_alignment_decode U,
        BernsteinPolynomialTasteGate_single_carrier_alignment_decode M,
        BernsteinPolynomialTasteGate_single_carrier_alignment_decode S,
        BernsteinPolynomialTasteGate_single_carrier_alignment_decode K,
        BernsteinPolynomialTasteGate_single_carrier_alignment_decode E,
        BernsteinPolynomialTasteGate_single_carrier_alignment_decode H,
        BernsteinPolynomialTasteGate_single_carrier_alignment_decode C,
        BernsteinPolynomialTasteGate_single_carrier_alignment_decode P,
        BernsteinPolynomialTasteGate_single_carrier_alignment_decode N]

private theorem BernsteinPolynomialTasteGate_single_carrier_alignment_injective
    {x y : BernsteinPolynomialUp} :
    bernsteinPolynomialToEventFlow x = bernsteinPolynomialToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bernsteinPolynomialFromEventFlow (bernsteinPolynomialToEventFlow x) =
        bernsteinPolynomialFromEventFlow (bernsteinPolynomialToEventFlow y) :=
    congrArg bernsteinPolynomialFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BernsteinPolynomialTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BernsteinPolynomialTasteGate_single_carrier_alignment_round_trip y)))

private theorem BernsteinPolynomialTasteGate_single_carrier_alignment_fields :
    ∀ x y : BernsteinPolynomialUp,
      bernsteinPolynomialFields x = bernsteinPolynomialFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 F1 U1 M1 S1 K1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 F2 U2 M2 S2 K2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance bernsteinPolynomialBHistCarrier : BHistCarrier BernsteinPolynomialUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bernsteinPolynomialToEventFlow
  fromEventFlow := bernsteinPolynomialFromEventFlow

instance bernsteinPolynomialChapterTasteGate :
    ChapterTasteGate BernsteinPolynomialUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bernsteinPolynomialFromEventFlow (bernsteinPolynomialToEventFlow x) =
      some x
    exact BernsteinPolynomialTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BernsteinPolynomialTasteGate_single_carrier_alignment_injective heq)

instance bernsteinPolynomialFieldFaithful :
    FieldFaithful BernsteinPolynomialUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bernsteinPolynomialFields
  field_faithful := BernsteinPolynomialTasteGate_single_carrier_alignment_fields

theorem BernsteinPolynomialTasteGate_single_carrier_alignment :
    (∀ h : BHist, bernsteinPolynomialDecodeBHist
      (bernsteinPolynomialEncodeBHist h) = h) ∧
      (∀ x : BernsteinPolynomialUp,
        bernsteinPolynomialFromEventFlow (bernsteinPolynomialToEventFlow x) =
          some x) ∧
        (∀ x y : BernsteinPolynomialUp,
          bernsteinPolynomialToEventFlow x = bernsteinPolynomialToEventFlow y →
            x = y) ∧
          bernsteinPolynomialEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨BernsteinPolynomialTasteGate_single_carrier_alignment_decode,
      BernsteinPolynomialTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => BernsteinPolynomialTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.BernsteinPolynomialUp
