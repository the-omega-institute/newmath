import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BareissFractionFreeEliminationUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BareissFractionFreeEliminationUp : Type where
  | mk (R M P D I L U Q X H C K N : BHist) : BareissFractionFreeEliminationUp
  deriving DecidableEq

def bareissFractionFreeEliminationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bareissFractionFreeEliminationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bareissFractionFreeEliminationEncodeBHist h

def bareissFractionFreeEliminationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bareissFractionFreeEliminationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bareissFractionFreeEliminationDecodeBHist tail)

private theorem bareissFractionFreeElimination_decode_encode_bhist :
    ∀ h : BHist,
      bareissFractionFreeEliminationDecodeBHist
          (bareissFractionFreeEliminationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def bareissFractionFreeEliminationFields :
    BareissFractionFreeEliminationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BareissFractionFreeEliminationUp.mk R M P D I L U Q X H C K N =>
      [R, M, P, D, I, L, U, Q, X, H, C, K, N]

def bareissFractionFreeEliminationToEventFlow :
    BareissFractionFreeEliminationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BareissFractionFreeEliminationUp.mk R M P D I L U Q X H C K N =>
      [bareissFractionFreeEliminationEncodeBHist R,
        bareissFractionFreeEliminationEncodeBHist M,
        bareissFractionFreeEliminationEncodeBHist P,
        bareissFractionFreeEliminationEncodeBHist D,
        bareissFractionFreeEliminationEncodeBHist I,
        bareissFractionFreeEliminationEncodeBHist L,
        bareissFractionFreeEliminationEncodeBHist U,
        bareissFractionFreeEliminationEncodeBHist Q,
        bareissFractionFreeEliminationEncodeBHist X,
        bareissFractionFreeEliminationEncodeBHist H,
        bareissFractionFreeEliminationEncodeBHist C,
        bareissFractionFreeEliminationEncodeBHist K,
        bareissFractionFreeEliminationEncodeBHist N]

private def bareissFractionFreeEliminationRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => bareissFractionFreeEliminationRawAt n rest

private def bareissFractionFreeEliminationLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => bareissFractionFreeEliminationLengthEq n rest

def bareissFractionFreeEliminationFromEventFlow :
    EventFlow → Option BareissFractionFreeEliminationUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match bareissFractionFreeEliminationLengthEq 13 flow with
      | true =>
          some
            (BareissFractionFreeEliminationUp.mk
              (bareissFractionFreeEliminationDecodeBHist
                (bareissFractionFreeEliminationRawAt 0 flow))
              (bareissFractionFreeEliminationDecodeBHist
                (bareissFractionFreeEliminationRawAt 1 flow))
              (bareissFractionFreeEliminationDecodeBHist
                (bareissFractionFreeEliminationRawAt 2 flow))
              (bareissFractionFreeEliminationDecodeBHist
                (bareissFractionFreeEliminationRawAt 3 flow))
              (bareissFractionFreeEliminationDecodeBHist
                (bareissFractionFreeEliminationRawAt 4 flow))
              (bareissFractionFreeEliminationDecodeBHist
                (bareissFractionFreeEliminationRawAt 5 flow))
              (bareissFractionFreeEliminationDecodeBHist
                (bareissFractionFreeEliminationRawAt 6 flow))
              (bareissFractionFreeEliminationDecodeBHist
                (bareissFractionFreeEliminationRawAt 7 flow))
              (bareissFractionFreeEliminationDecodeBHist
                (bareissFractionFreeEliminationRawAt 8 flow))
              (bareissFractionFreeEliminationDecodeBHist
                (bareissFractionFreeEliminationRawAt 9 flow))
              (bareissFractionFreeEliminationDecodeBHist
                (bareissFractionFreeEliminationRawAt 10 flow))
              (bareissFractionFreeEliminationDecodeBHist
                (bareissFractionFreeEliminationRawAt 11 flow))
              (bareissFractionFreeEliminationDecodeBHist
                (bareissFractionFreeEliminationRawAt 12 flow)))
      | false => none

private theorem bareissFractionFreeElimination_round_trip :
    ∀ x : BareissFractionFreeEliminationUp,
      bareissFractionFreeEliminationFromEventFlow
          (bareissFractionFreeEliminationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R M P D I L U Q X H C K N =>
      change
        some
          (BareissFractionFreeEliminationUp.mk
            (bareissFractionFreeEliminationDecodeBHist
              (bareissFractionFreeEliminationEncodeBHist R))
            (bareissFractionFreeEliminationDecodeBHist
              (bareissFractionFreeEliminationEncodeBHist M))
            (bareissFractionFreeEliminationDecodeBHist
              (bareissFractionFreeEliminationEncodeBHist P))
            (bareissFractionFreeEliminationDecodeBHist
              (bareissFractionFreeEliminationEncodeBHist D))
            (bareissFractionFreeEliminationDecodeBHist
              (bareissFractionFreeEliminationEncodeBHist I))
            (bareissFractionFreeEliminationDecodeBHist
              (bareissFractionFreeEliminationEncodeBHist L))
            (bareissFractionFreeEliminationDecodeBHist
              (bareissFractionFreeEliminationEncodeBHist U))
            (bareissFractionFreeEliminationDecodeBHist
              (bareissFractionFreeEliminationEncodeBHist Q))
            (bareissFractionFreeEliminationDecodeBHist
              (bareissFractionFreeEliminationEncodeBHist X))
            (bareissFractionFreeEliminationDecodeBHist
              (bareissFractionFreeEliminationEncodeBHist H))
            (bareissFractionFreeEliminationDecodeBHist
              (bareissFractionFreeEliminationEncodeBHist C))
            (bareissFractionFreeEliminationDecodeBHist
              (bareissFractionFreeEliminationEncodeBHist K))
            (bareissFractionFreeEliminationDecodeBHist
              (bareissFractionFreeEliminationEncodeBHist N))) =
          some (BareissFractionFreeEliminationUp.mk R M P D I L U Q X H C K N)
      rw [bareissFractionFreeElimination_decode_encode_bhist R,
        bareissFractionFreeElimination_decode_encode_bhist M,
        bareissFractionFreeElimination_decode_encode_bhist P,
        bareissFractionFreeElimination_decode_encode_bhist D,
        bareissFractionFreeElimination_decode_encode_bhist I,
        bareissFractionFreeElimination_decode_encode_bhist L,
        bareissFractionFreeElimination_decode_encode_bhist U,
        bareissFractionFreeElimination_decode_encode_bhist Q,
        bareissFractionFreeElimination_decode_encode_bhist X,
        bareissFractionFreeElimination_decode_encode_bhist H,
        bareissFractionFreeElimination_decode_encode_bhist C,
        bareissFractionFreeElimination_decode_encode_bhist K,
        bareissFractionFreeElimination_decode_encode_bhist N]

private theorem bareissFractionFreeEliminationToEventFlow_injective
    {x y : BareissFractionFreeEliminationUp} :
    bareissFractionFreeEliminationToEventFlow x =
        bareissFractionFreeEliminationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bareissFractionFreeEliminationFromEventFlow
          (bareissFractionFreeEliminationToEventFlow x) =
        bareissFractionFreeEliminationFromEventFlow
          (bareissFractionFreeEliminationToEventFlow y) :=
    congrArg bareissFractionFreeEliminationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bareissFractionFreeElimination_round_trip x).symm
      (Eq.trans hread (bareissFractionFreeElimination_round_trip y)))

private theorem bareissFractionFreeElimination_field_faithful :
    ∀ x y : BareissFractionFreeEliminationUp,
      bareissFractionFreeEliminationFields x =
        bareissFractionFreeEliminationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk R1 M1 P1 D1 I1 L1 U1 Q1 X1 H1 C1 K1 N1 =>
      cases y with
      | mk R2 M2 P2 D2 I2 L2 U2 Q2 X2 H2 C2 K2 N2 =>
          cases h
          rfl

instance bareissFractionFreeEliminationBHistCarrier :
    BHistCarrier BareissFractionFreeEliminationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bareissFractionFreeEliminationToEventFlow
  fromEventFlow := bareissFractionFreeEliminationFromEventFlow

instance bareissFractionFreeEliminationChapterTasteGate :
    ChapterTasteGate BareissFractionFreeEliminationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bareissFractionFreeEliminationFromEventFlow
          (bareissFractionFreeEliminationToEventFlow x) = some x
    exact bareissFractionFreeElimination_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bareissFractionFreeEliminationToEventFlow_injective heq)

instance bareissFractionFreeEliminationFieldFaithful :
    FieldFaithful BareissFractionFreeEliminationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bareissFractionFreeEliminationFields
  field_faithful := bareissFractionFreeElimination_field_faithful

instance bareissFractionFreeEliminationNontrivial :
    Nontrivial BareissFractionFreeEliminationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BareissFractionFreeEliminationUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BareissFractionFreeEliminationUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BareissFractionFreeEliminationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bareissFractionFreeEliminationChapterTasteGate

theorem BareissFractionFreeEliminationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bareissFractionFreeEliminationDecodeBHist
        (bareissFractionFreeEliminationEncodeBHist h) = h) ∧
      (∀ x : BareissFractionFreeEliminationUp,
        bareissFractionFreeEliminationFromEventFlow
          (bareissFractionFreeEliminationToEventFlow x) = some x) ∧
        (∀ x y : BareissFractionFreeEliminationUp,
          bareissFractionFreeEliminationToEventFlow x =
            bareissFractionFreeEliminationToEventFlow y → x = y) ∧
          bareissFractionFreeEliminationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨bareissFractionFreeElimination_decode_encode_bhist,
      bareissFractionFreeElimination_round_trip,
      by
        intro x y heq
        exact bareissFractionFreeEliminationToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.BareissFractionFreeEliminationUp.TasteGate
