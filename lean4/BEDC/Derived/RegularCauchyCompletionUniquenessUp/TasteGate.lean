import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyCompletionUniquenessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyCompletionUniquenessUp : Type where
  | mk (L R D S Q E T H C P N : BHist) : RegularCauchyCompletionUniquenessUp
  deriving DecidableEq

def regularCauchyCompletionUniquenessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyCompletionUniquenessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyCompletionUniquenessEncodeBHist h

def regularCauchyCompletionUniquenessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyCompletionUniquenessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyCompletionUniquenessDecodeBHist tail)

private theorem regularCauchyCompletionUniqueness_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchyCompletionUniquenessDecodeBHist
          (regularCauchyCompletionUniquenessEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyCompletionUniquenessFields :
    RegularCauchyCompletionUniquenessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyCompletionUniquenessUp.mk L R D S Q E T H C P N =>
      [L, R, D, S, Q, E, T, H, C, P, N]

def regularCauchyCompletionUniquenessToEventFlow :
    RegularCauchyCompletionUniquenessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (regularCauchyCompletionUniquenessFields x).map
        regularCauchyCompletionUniquenessEncodeBHist

private def regularCauchyCompletionUniquenessRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => regularCauchyCompletionUniquenessRawAt n rest

private def regularCauchyCompletionUniquenessLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => regularCauchyCompletionUniquenessLengthEq n rest

def regularCauchyCompletionUniquenessFromEventFlow :
    EventFlow → Option RegularCauchyCompletionUniquenessUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match regularCauchyCompletionUniquenessLengthEq 11 flow with
      | true =>
          some
            (RegularCauchyCompletionUniquenessUp.mk
              (regularCauchyCompletionUniquenessDecodeBHist
                (regularCauchyCompletionUniquenessRawAt 0 flow))
              (regularCauchyCompletionUniquenessDecodeBHist
                (regularCauchyCompletionUniquenessRawAt 1 flow))
              (regularCauchyCompletionUniquenessDecodeBHist
                (regularCauchyCompletionUniquenessRawAt 2 flow))
              (regularCauchyCompletionUniquenessDecodeBHist
                (regularCauchyCompletionUniquenessRawAt 3 flow))
              (regularCauchyCompletionUniquenessDecodeBHist
                (regularCauchyCompletionUniquenessRawAt 4 flow))
              (regularCauchyCompletionUniquenessDecodeBHist
                (regularCauchyCompletionUniquenessRawAt 5 flow))
              (regularCauchyCompletionUniquenessDecodeBHist
                (regularCauchyCompletionUniquenessRawAt 6 flow))
              (regularCauchyCompletionUniquenessDecodeBHist
                (regularCauchyCompletionUniquenessRawAt 7 flow))
              (regularCauchyCompletionUniquenessDecodeBHist
                (regularCauchyCompletionUniquenessRawAt 8 flow))
              (regularCauchyCompletionUniquenessDecodeBHist
                (regularCauchyCompletionUniquenessRawAt 9 flow))
              (regularCauchyCompletionUniquenessDecodeBHist
                (regularCauchyCompletionUniquenessRawAt 10 flow)))
      | false => none

private theorem regularCauchyCompletionUniqueness_round_trip :
    ∀ x : RegularCauchyCompletionUniquenessUp,
      regularCauchyCompletionUniquenessFromEventFlow
          (regularCauchyCompletionUniquenessToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L R D S Q E T H C P N =>
      change
        some
          (RegularCauchyCompletionUniquenessUp.mk
            (regularCauchyCompletionUniquenessDecodeBHist
              (regularCauchyCompletionUniquenessEncodeBHist L))
            (regularCauchyCompletionUniquenessDecodeBHist
              (regularCauchyCompletionUniquenessEncodeBHist R))
            (regularCauchyCompletionUniquenessDecodeBHist
              (regularCauchyCompletionUniquenessEncodeBHist D))
            (regularCauchyCompletionUniquenessDecodeBHist
              (regularCauchyCompletionUniquenessEncodeBHist S))
            (regularCauchyCompletionUniquenessDecodeBHist
              (regularCauchyCompletionUniquenessEncodeBHist Q))
            (regularCauchyCompletionUniquenessDecodeBHist
              (regularCauchyCompletionUniquenessEncodeBHist E))
            (regularCauchyCompletionUniquenessDecodeBHist
              (regularCauchyCompletionUniquenessEncodeBHist T))
            (regularCauchyCompletionUniquenessDecodeBHist
              (regularCauchyCompletionUniquenessEncodeBHist H))
            (regularCauchyCompletionUniquenessDecodeBHist
              (regularCauchyCompletionUniquenessEncodeBHist C))
            (regularCauchyCompletionUniquenessDecodeBHist
              (regularCauchyCompletionUniquenessEncodeBHist P))
            (regularCauchyCompletionUniquenessDecodeBHist
              (regularCauchyCompletionUniquenessEncodeBHist N))) =
          some (RegularCauchyCompletionUniquenessUp.mk L R D S Q E T H C P N)
      rw [regularCauchyCompletionUniqueness_decode_encode_bhist L,
        regularCauchyCompletionUniqueness_decode_encode_bhist R,
        regularCauchyCompletionUniqueness_decode_encode_bhist D,
        regularCauchyCompletionUniqueness_decode_encode_bhist S,
        regularCauchyCompletionUniqueness_decode_encode_bhist Q,
        regularCauchyCompletionUniqueness_decode_encode_bhist E,
        regularCauchyCompletionUniqueness_decode_encode_bhist T,
        regularCauchyCompletionUniqueness_decode_encode_bhist H,
        regularCauchyCompletionUniqueness_decode_encode_bhist C,
        regularCauchyCompletionUniqueness_decode_encode_bhist P,
        regularCauchyCompletionUniqueness_decode_encode_bhist N]

private theorem regularCauchyCompletionUniquenessToEventFlow_injective
    {x y : RegularCauchyCompletionUniquenessUp} :
    regularCauchyCompletionUniquenessToEventFlow x =
        regularCauchyCompletionUniquenessToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyCompletionUniquenessFromEventFlow
          (regularCauchyCompletionUniquenessToEventFlow x) =
        regularCauchyCompletionUniquenessFromEventFlow
          (regularCauchyCompletionUniquenessToEventFlow y) :=
    congrArg regularCauchyCompletionUniquenessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyCompletionUniqueness_round_trip x).symm
      (Eq.trans hread (regularCauchyCompletionUniqueness_round_trip y)))

private theorem regularCauchyCompletionUniqueness_field_faithful :
    ∀ x y : RegularCauchyCompletionUniquenessUp,
      regularCauchyCompletionUniquenessFields x =
          regularCauchyCompletionUniquenessFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L1 R1 D1 S1 Q1 E1 T1 H1 C1 P1 N1 =>
      cases y with
      | mk L2 R2 D2 S2 Q2 E2 T2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance regularCauchyCompletionUniquenessBHistCarrier :
    BHistCarrier RegularCauchyCompletionUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyCompletionUniquenessToEventFlow
  fromEventFlow := regularCauchyCompletionUniquenessFromEventFlow

instance regularCauchyCompletionUniquenessChapterTasteGate :
    ChapterTasteGate RegularCauchyCompletionUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyCompletionUniquenessFromEventFlow
          (regularCauchyCompletionUniquenessToEventFlow x) =
        some x
    exact regularCauchyCompletionUniqueness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyCompletionUniquenessToEventFlow_injective heq)

instance regularCauchyCompletionUniquenessFieldFaithful :
    FieldFaithful RegularCauchyCompletionUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyCompletionUniquenessFields
  field_faithful := regularCauchyCompletionUniqueness_field_faithful

instance regularCauchyCompletionUniquenessNontrivial :
    Nontrivial RegularCauchyCompletionUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyCompletionUniquenessUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RegularCauchyCompletionUniquenessUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyCompletionUniquenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyCompletionUniquenessChapterTasteGate

theorem RegularCauchyCompletionUniquenessUpTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyCompletionUniquenessDecodeBHist
        (regularCauchyCompletionUniquenessEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyCompletionUniquenessUp,
        regularCauchyCompletionUniquenessFromEventFlow
          (regularCauchyCompletionUniquenessToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyCompletionUniquenessUp,
          regularCauchyCompletionUniquenessToEventFlow x =
            regularCauchyCompletionUniquenessToEventFlow y → x = y) ∧
          regularCauchyCompletionUniquenessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨regularCauchyCompletionUniqueness_decode_encode_bhist,
      regularCauchyCompletionUniqueness_round_trip,
      by
        intro x y heq
        exact regularCauchyCompletionUniquenessToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RegularCauchyCompletionUniquenessUp
