import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DedekindCutCauchyBoundaryUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DedekindCutCauchyBoundaryUp : Type where
  | mk (L U K Q S R D E H C P N : BHist) : DedekindCutCauchyBoundaryUp
  deriving DecidableEq

def dedekindCutCauchyBoundaryUpEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dedekindCutCauchyBoundaryUpEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dedekindCutCauchyBoundaryUpEncodeBHist h

def dedekindCutCauchyBoundaryUpDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dedekindCutCauchyBoundaryUpDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dedekindCutCauchyBoundaryUpDecodeBHist tail)

private theorem dedekindCutCauchyBoundaryUpDecode_encode_bhist :
    ∀ h : BHist,
      dedekindCutCauchyBoundaryUpDecodeBHist
          (dedekindCutCauchyBoundaryUpEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dedekindCutCauchyBoundaryUpFields :
    DedekindCutCauchyBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DedekindCutCauchyBoundaryUp.mk L U K Q S R D E H C P N =>
      [L, U, K, Q, S, R, D, E, H, C, P, N]

def dedekindCutCauchyBoundaryUpToEventFlow :
    DedekindCutCauchyBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (dedekindCutCauchyBoundaryUpFields x).map
        dedekindCutCauchyBoundaryUpEncodeBHist

private def dedekindCutCauchyBoundaryUpRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => dedekindCutCauchyBoundaryUpRawAt n rest

private def dedekindCutCauchyBoundaryUpLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => dedekindCutCauchyBoundaryUpLengthEq n rest

def dedekindCutCauchyBoundaryUpFromEventFlow :
    EventFlow → Option DedekindCutCauchyBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match dedekindCutCauchyBoundaryUpLengthEq 12 flow with
      | true =>
          some
            (DedekindCutCauchyBoundaryUp.mk
              (dedekindCutCauchyBoundaryUpDecodeBHist
                (dedekindCutCauchyBoundaryUpRawAt 0 flow))
              (dedekindCutCauchyBoundaryUpDecodeBHist
                (dedekindCutCauchyBoundaryUpRawAt 1 flow))
              (dedekindCutCauchyBoundaryUpDecodeBHist
                (dedekindCutCauchyBoundaryUpRawAt 2 flow))
              (dedekindCutCauchyBoundaryUpDecodeBHist
                (dedekindCutCauchyBoundaryUpRawAt 3 flow))
              (dedekindCutCauchyBoundaryUpDecodeBHist
                (dedekindCutCauchyBoundaryUpRawAt 4 flow))
              (dedekindCutCauchyBoundaryUpDecodeBHist
                (dedekindCutCauchyBoundaryUpRawAt 5 flow))
              (dedekindCutCauchyBoundaryUpDecodeBHist
                (dedekindCutCauchyBoundaryUpRawAt 6 flow))
              (dedekindCutCauchyBoundaryUpDecodeBHist
                (dedekindCutCauchyBoundaryUpRawAt 7 flow))
              (dedekindCutCauchyBoundaryUpDecodeBHist
                (dedekindCutCauchyBoundaryUpRawAt 8 flow))
              (dedekindCutCauchyBoundaryUpDecodeBHist
                (dedekindCutCauchyBoundaryUpRawAt 9 flow))
              (dedekindCutCauchyBoundaryUpDecodeBHist
                (dedekindCutCauchyBoundaryUpRawAt 10 flow))
              (dedekindCutCauchyBoundaryUpDecodeBHist
                (dedekindCutCauchyBoundaryUpRawAt 11 flow)))
      | false => none

private theorem dedekindCutCauchyBoundaryUp_round_trip :
    ∀ x : DedekindCutCauchyBoundaryUp,
      dedekindCutCauchyBoundaryUpFromEventFlow
          (dedekindCutCauchyBoundaryUpToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U K Q S R D E H C P N =>
      change
        some
          (DedekindCutCauchyBoundaryUp.mk
            (dedekindCutCauchyBoundaryUpDecodeBHist
              (dedekindCutCauchyBoundaryUpEncodeBHist L))
            (dedekindCutCauchyBoundaryUpDecodeBHist
              (dedekindCutCauchyBoundaryUpEncodeBHist U))
            (dedekindCutCauchyBoundaryUpDecodeBHist
              (dedekindCutCauchyBoundaryUpEncodeBHist K))
            (dedekindCutCauchyBoundaryUpDecodeBHist
              (dedekindCutCauchyBoundaryUpEncodeBHist Q))
            (dedekindCutCauchyBoundaryUpDecodeBHist
              (dedekindCutCauchyBoundaryUpEncodeBHist S))
            (dedekindCutCauchyBoundaryUpDecodeBHist
              (dedekindCutCauchyBoundaryUpEncodeBHist R))
            (dedekindCutCauchyBoundaryUpDecodeBHist
              (dedekindCutCauchyBoundaryUpEncodeBHist D))
            (dedekindCutCauchyBoundaryUpDecodeBHist
              (dedekindCutCauchyBoundaryUpEncodeBHist E))
            (dedekindCutCauchyBoundaryUpDecodeBHist
              (dedekindCutCauchyBoundaryUpEncodeBHist H))
            (dedekindCutCauchyBoundaryUpDecodeBHist
              (dedekindCutCauchyBoundaryUpEncodeBHist C))
            (dedekindCutCauchyBoundaryUpDecodeBHist
              (dedekindCutCauchyBoundaryUpEncodeBHist P))
            (dedekindCutCauchyBoundaryUpDecodeBHist
              (dedekindCutCauchyBoundaryUpEncodeBHist N))) =
          some (DedekindCutCauchyBoundaryUp.mk L U K Q S R D E H C P N)
      rw [dedekindCutCauchyBoundaryUpDecode_encode_bhist L,
        dedekindCutCauchyBoundaryUpDecode_encode_bhist U,
        dedekindCutCauchyBoundaryUpDecode_encode_bhist K,
        dedekindCutCauchyBoundaryUpDecode_encode_bhist Q,
        dedekindCutCauchyBoundaryUpDecode_encode_bhist S,
        dedekindCutCauchyBoundaryUpDecode_encode_bhist R,
        dedekindCutCauchyBoundaryUpDecode_encode_bhist D,
        dedekindCutCauchyBoundaryUpDecode_encode_bhist E,
        dedekindCutCauchyBoundaryUpDecode_encode_bhist H,
        dedekindCutCauchyBoundaryUpDecode_encode_bhist C,
        dedekindCutCauchyBoundaryUpDecode_encode_bhist P,
        dedekindCutCauchyBoundaryUpDecode_encode_bhist N]

private theorem dedekindCutCauchyBoundaryUpToEventFlow_injective
    {x y : DedekindCutCauchyBoundaryUp} :
    dedekindCutCauchyBoundaryUpToEventFlow x =
        dedekindCutCauchyBoundaryUpToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dedekindCutCauchyBoundaryUpFromEventFlow
          (dedekindCutCauchyBoundaryUpToEventFlow x) =
        dedekindCutCauchyBoundaryUpFromEventFlow
          (dedekindCutCauchyBoundaryUpToEventFlow y) :=
    congrArg dedekindCutCauchyBoundaryUpFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dedekindCutCauchyBoundaryUp_round_trip x).symm
      (Eq.trans hread (dedekindCutCauchyBoundaryUp_round_trip y)))

private theorem dedekindCutCauchyBoundaryUp_field_faithful :
    ∀ x y : DedekindCutCauchyBoundaryUp,
      dedekindCutCauchyBoundaryUpFields x = dedekindCutCauchyBoundaryUpFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L1 U1 K1 Q1 S1 R1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk L2 U2 K2 Q2 S2 R2 D2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance dedekindCutCauchyBoundaryUpBHistCarrier :
    BHistCarrier DedekindCutCauchyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dedekindCutCauchyBoundaryUpToEventFlow
  fromEventFlow := dedekindCutCauchyBoundaryUpFromEventFlow

instance dedekindCutCauchyBoundaryUpChapterTasteGate :
    ChapterTasteGate DedekindCutCauchyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dedekindCutCauchyBoundaryUpFromEventFlow
          (dedekindCutCauchyBoundaryUpToEventFlow x) =
        some x
    exact dedekindCutCauchyBoundaryUp_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dedekindCutCauchyBoundaryUpToEventFlow_injective heq)

instance dedekindCutCauchyBoundaryUpFieldFaithful :
    FieldFaithful DedekindCutCauchyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dedekindCutCauchyBoundaryUpFields
  field_faithful := dedekindCutCauchyBoundaryUp_field_faithful

def taste_gate : ChapterTasteGate DedekindCutCauchyBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dedekindCutCauchyBoundaryUpChapterTasteGate

theorem DedekindCutCauchyBoundaryUpTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DedekindCutCauchyBoundaryUp) ∧
      Nonempty (FieldFaithful DedekindCutCauchyBoundaryUp) ∧
      (∀ h : BHist,
        dedekindCutCauchyBoundaryUpDecodeBHist
            (dedekindCutCauchyBoundaryUpEncodeBHist h) =
          h) ∧
      (∀ x : DedekindCutCauchyBoundaryUp,
        dedekindCutCauchyBoundaryUpFromEventFlow
            (dedekindCutCauchyBoundaryUpToEventFlow x) =
          some x) ∧
      dedekindCutCauchyBoundaryUpEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨Nonempty.intro dedekindCutCauchyBoundaryUpChapterTasteGate,
      Nonempty.intro dedekindCutCauchyBoundaryUpFieldFaithful,
      dedekindCutCauchyBoundaryUpDecode_encode_bhist,
      dedekindCutCauchyBoundaryUp_round_trip,
      rfl⟩

end BEDC.Derived.DedekindCutCauchyBoundaryUp.TasteGate
