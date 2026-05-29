import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyUniquenessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyUniquenessUp : Type where
  | mk (X Y S T D E R H C P N : BHist) : RegularCauchyUniquenessUp
  deriving DecidableEq

def regularCauchyUniquenessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyUniquenessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyUniquenessEncodeBHist h

def regularCauchyUniquenessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyUniquenessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyUniquenessDecodeBHist tail)

private theorem regularCauchyUniqueness_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchyUniquenessDecodeBHist (regularCauchyUniquenessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyUniquenessToEventFlow : RegularCauchyUniquenessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyUniquenessUp.mk X Y S T D E R H C P N =>
      [regularCauchyUniquenessEncodeBHist X,
        regularCauchyUniquenessEncodeBHist Y,
        regularCauchyUniquenessEncodeBHist S,
        regularCauchyUniquenessEncodeBHist T,
        regularCauchyUniquenessEncodeBHist D,
        regularCauchyUniquenessEncodeBHist E,
        regularCauchyUniquenessEncodeBHist R,
        regularCauchyUniquenessEncodeBHist H,
        regularCauchyUniquenessEncodeBHist C,
        regularCauchyUniquenessEncodeBHist P,
        regularCauchyUniquenessEncodeBHist N]

private def regularCauchyUniquenessEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyUniquenessEventAtDefault index rest

def regularCauchyUniquenessFromEventFlow
    (ef : EventFlow) : Option RegularCauchyUniquenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyUniquenessUp.mk
      (regularCauchyUniquenessDecodeBHist (regularCauchyUniquenessEventAtDefault 0 ef))
      (regularCauchyUniquenessDecodeBHist (regularCauchyUniquenessEventAtDefault 1 ef))
      (regularCauchyUniquenessDecodeBHist (regularCauchyUniquenessEventAtDefault 2 ef))
      (regularCauchyUniquenessDecodeBHist (regularCauchyUniquenessEventAtDefault 3 ef))
      (regularCauchyUniquenessDecodeBHist (regularCauchyUniquenessEventAtDefault 4 ef))
      (regularCauchyUniquenessDecodeBHist (regularCauchyUniquenessEventAtDefault 5 ef))
      (regularCauchyUniquenessDecodeBHist (regularCauchyUniquenessEventAtDefault 6 ef))
      (regularCauchyUniquenessDecodeBHist (regularCauchyUniquenessEventAtDefault 7 ef))
      (regularCauchyUniquenessDecodeBHist (regularCauchyUniquenessEventAtDefault 8 ef))
      (regularCauchyUniquenessDecodeBHist (regularCauchyUniquenessEventAtDefault 9 ef))
      (regularCauchyUniquenessDecodeBHist (regularCauchyUniquenessEventAtDefault 10 ef)))

private theorem regularCauchyUniqueness_round_trip :
    ∀ x : RegularCauchyUniquenessUp,
      regularCauchyUniquenessFromEventFlow (regularCauchyUniquenessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y S T D E R H C P N =>
      change
        some
            (RegularCauchyUniquenessUp.mk
              (regularCauchyUniquenessDecodeBHist (regularCauchyUniquenessEncodeBHist X))
              (regularCauchyUniquenessDecodeBHist (regularCauchyUniquenessEncodeBHist Y))
              (regularCauchyUniquenessDecodeBHist (regularCauchyUniquenessEncodeBHist S))
              (regularCauchyUniquenessDecodeBHist (regularCauchyUniquenessEncodeBHist T))
              (regularCauchyUniquenessDecodeBHist (regularCauchyUniquenessEncodeBHist D))
              (regularCauchyUniquenessDecodeBHist (regularCauchyUniquenessEncodeBHist E))
              (regularCauchyUniquenessDecodeBHist (regularCauchyUniquenessEncodeBHist R))
              (regularCauchyUniquenessDecodeBHist (regularCauchyUniquenessEncodeBHist H))
              (regularCauchyUniquenessDecodeBHist (regularCauchyUniquenessEncodeBHist C))
              (regularCauchyUniquenessDecodeBHist (regularCauchyUniquenessEncodeBHist P))
              (regularCauchyUniquenessDecodeBHist (regularCauchyUniquenessEncodeBHist N))) =
          some (RegularCauchyUniquenessUp.mk X Y S T D E R H C P N)
      rw [regularCauchyUniqueness_decode_encode_bhist X,
        regularCauchyUniqueness_decode_encode_bhist Y,
        regularCauchyUniqueness_decode_encode_bhist S,
        regularCauchyUniqueness_decode_encode_bhist T,
        regularCauchyUniqueness_decode_encode_bhist D,
        regularCauchyUniqueness_decode_encode_bhist E,
        regularCauchyUniqueness_decode_encode_bhist R,
        regularCauchyUniqueness_decode_encode_bhist H,
        regularCauchyUniqueness_decode_encode_bhist C,
        regularCauchyUniqueness_decode_encode_bhist P,
        regularCauchyUniqueness_decode_encode_bhist N]

private theorem regularCauchyUniquenessToEventFlow_injective
    {x y : RegularCauchyUniquenessUp} :
    regularCauchyUniquenessToEventFlow x = regularCauchyUniquenessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyUniquenessFromEventFlow (regularCauchyUniquenessToEventFlow x) =
        regularCauchyUniquenessFromEventFlow (regularCauchyUniquenessToEventFlow y) :=
    congrArg regularCauchyUniquenessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyUniqueness_round_trip x).symm
      (Eq.trans hread (regularCauchyUniqueness_round_trip y)))

def regularCauchyUniquenessFields : RegularCauchyUniquenessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyUniquenessUp.mk X Y S T D E R H C P N => [X, Y, S, T, D, E, R, H, C, P, N]

private theorem regularCauchyUniqueness_fields_faithful :
    ∀ x y : RegularCauchyUniquenessUp,
      regularCauchyUniquenessFields x = regularCauchyUniquenessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk X Y S T D E R H C P N =>
      cases y with
      | mk X' Y' S' T' D' E' R' H' C' P' N' =>
          simp only [regularCauchyUniquenessFields] at h
          cases h
          rfl

instance regularCauchyUniquenessBHistCarrier : BHistCarrier RegularCauchyUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyUniquenessToEventFlow
  fromEventFlow := regularCauchyUniquenessFromEventFlow

instance regularCauchyUniquenessChapterTasteGate :
    ChapterTasteGate RegularCauchyUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyUniquenessFromEventFlow (regularCauchyUniquenessToEventFlow x) = some x
    exact regularCauchyUniqueness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyUniquenessToEventFlow_injective heq)

instance regularCauchyUniquenessFieldFaithful : FieldFaithful RegularCauchyUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyUniquenessFields
  field_faithful := regularCauchyUniqueness_fields_faithful

instance regularCauchyUniquenessNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RegularCauchyUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyUniquenessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyUniquenessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyUniquenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyUniquenessChapterTasteGate

theorem RegularCauchyUniquenessTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegularCauchyUniquenessUp) ∧
      Nonempty (FieldFaithful RegularCauchyUniquenessUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RegularCauchyUniquenessUp) ∧
          (∀ h : BHist,
            regularCauchyUniquenessDecodeBHist (regularCauchyUniquenessEncodeBHist h) = h) ∧
            (∀ x : RegularCauchyUniquenessUp,
              regularCauchyUniquenessFromEventFlow (regularCauchyUniquenessToEventFlow x) =
                some x) ∧
              (∀ x y : RegularCauchyUniquenessUp,
                regularCauchyUniquenessToEventFlow x =
                    regularCauchyUniquenessToEventFlow y →
                  x = y) ∧
                regularCauchyUniquenessEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨regularCauchyUniquenessChapterTasteGate⟩,
      ⟨regularCauchyUniquenessFieldFaithful⟩,
      ⟨regularCauchyUniquenessNontrivial⟩,
      regularCauchyUniqueness_decode_encode_bhist,
      regularCauchyUniqueness_round_trip,
      (fun _ _ heq => regularCauchyUniquenessToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyUniquenessUp
