import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyQuotientRefusalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyQuotientRefusalUp : Type where
  | mk (D S R E U H C P N : BHist) : RegularCauchyQuotientRefusalUp
  deriving DecidableEq

def regularCauchyQuotientRefusalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyQuotientRefusalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyQuotientRefusalEncodeBHist h

def regularCauchyQuotientRefusalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyQuotientRefusalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyQuotientRefusalDecodeBHist tail)

private theorem regularCauchyQuotientRefusalDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchyQuotientRefusalDecodeBHist
        (regularCauchyQuotientRefusalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyQuotientRefusalFields :
    RegularCauchyQuotientRefusalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyQuotientRefusalUp.mk D S R E U H C P N => [D, S, R, E, U, H, C, P, N]

def regularCauchyQuotientRefusalToEventFlow :
    RegularCauchyQuotientRefusalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyQuotientRefusalFields x).map
      regularCauchyQuotientRefusalEncodeBHist

def regularCauchyQuotientRefusalFromEventFlow :
    EventFlow → Option RegularCauchyQuotientRefusalUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | D :: restS =>
      match restS with
      | [] => none
      | S :: restR =>
          match restR with
          | [] => none
          | R :: restE =>
              match restE with
              | [] => none
              | E :: restU =>
                  match restU with
                  | [] => none
                  | U :: restH =>
                      match restH with
                      | [] => none
                      | H :: restC =>
                          match restC with
                          | [] => none
                          | C :: restP =>
                              match restP with
                              | [] => none
                              | P :: restN =>
                                  match restN with
                                  | [] => none
                                  | N :: rest =>
                                      match rest with
                                      | [] =>
                                          some
                                            (RegularCauchyQuotientRefusalUp.mk
                                              (regularCauchyQuotientRefusalDecodeBHist D)
                                              (regularCauchyQuotientRefusalDecodeBHist S)
                                              (regularCauchyQuotientRefusalDecodeBHist R)
                                              (regularCauchyQuotientRefusalDecodeBHist E)
                                              (regularCauchyQuotientRefusalDecodeBHist U)
                                              (regularCauchyQuotientRefusalDecodeBHist H)
                                              (regularCauchyQuotientRefusalDecodeBHist C)
                                              (regularCauchyQuotientRefusalDecodeBHist P)
                                              (regularCauchyQuotientRefusalDecodeBHist N))
                                      | _ :: _ => none

private theorem regularCauchyQuotientRefusal_round_trip :
    ∀ x : RegularCauchyQuotientRefusalUp,
      regularCauchyQuotientRefusalFromEventFlow
        (regularCauchyQuotientRefusalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R E U H C P N =>
      change
        some
          (RegularCauchyQuotientRefusalUp.mk
            (regularCauchyQuotientRefusalDecodeBHist
              (regularCauchyQuotientRefusalEncodeBHist D))
            (regularCauchyQuotientRefusalDecodeBHist
              (regularCauchyQuotientRefusalEncodeBHist S))
            (regularCauchyQuotientRefusalDecodeBHist
              (regularCauchyQuotientRefusalEncodeBHist R))
            (regularCauchyQuotientRefusalDecodeBHist
              (regularCauchyQuotientRefusalEncodeBHist E))
            (regularCauchyQuotientRefusalDecodeBHist
              (regularCauchyQuotientRefusalEncodeBHist U))
            (regularCauchyQuotientRefusalDecodeBHist
              (regularCauchyQuotientRefusalEncodeBHist H))
            (regularCauchyQuotientRefusalDecodeBHist
              (regularCauchyQuotientRefusalEncodeBHist C))
            (regularCauchyQuotientRefusalDecodeBHist
              (regularCauchyQuotientRefusalEncodeBHist P))
            (regularCauchyQuotientRefusalDecodeBHist
              (regularCauchyQuotientRefusalEncodeBHist N))) =
          some (RegularCauchyQuotientRefusalUp.mk D S R E U H C P N)
      rw [regularCauchyQuotientRefusalDecode_encode_bhist D,
        regularCauchyQuotientRefusalDecode_encode_bhist S,
        regularCauchyQuotientRefusalDecode_encode_bhist R,
        regularCauchyQuotientRefusalDecode_encode_bhist E,
        regularCauchyQuotientRefusalDecode_encode_bhist U,
        regularCauchyQuotientRefusalDecode_encode_bhist H,
        regularCauchyQuotientRefusalDecode_encode_bhist C,
        regularCauchyQuotientRefusalDecode_encode_bhist P,
        regularCauchyQuotientRefusalDecode_encode_bhist N]

private theorem regularCauchyQuotientRefusalToEventFlow_injective
    {x y : RegularCauchyQuotientRefusalUp} :
    regularCauchyQuotientRefusalToEventFlow x =
      regularCauchyQuotientRefusalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyQuotientRefusalFromEventFlow
          (regularCauchyQuotientRefusalToEventFlow x) =
        regularCauchyQuotientRefusalFromEventFlow
          (regularCauchyQuotientRefusalToEventFlow y) :=
    congrArg regularCauchyQuotientRefusalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyQuotientRefusal_round_trip x).symm
      (Eq.trans hread (regularCauchyQuotientRefusal_round_trip y)))

instance regularCauchyQuotientRefusalBHistCarrier :
    BHistCarrier RegularCauchyQuotientRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyQuotientRefusalToEventFlow
  fromEventFlow := regularCauchyQuotientRefusalFromEventFlow

instance regularCauchyQuotientRefusalChapterTasteGate :
    ChapterTasteGate RegularCauchyQuotientRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyQuotientRefusalFromEventFlow
        (regularCauchyQuotientRefusalToEventFlow x) = some x
    exact regularCauchyQuotientRefusal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyQuotientRefusalToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyQuotientRefusalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyQuotientRefusalChapterTasteGate

theorem RegularCauchyQuotientRefusalTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyQuotientRefusalDecodeBHist
        (regularCauchyQuotientRefusalEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyQuotientRefusalUp,
        regularCauchyQuotientRefusalFromEventFlow
          (regularCauchyQuotientRefusalToEventFlow x) = some x) ∧
      (∀ x y : RegularCauchyQuotientRefusalUp,
        regularCauchyQuotientRefusalToEventFlow x =
          regularCauchyQuotientRefusalToEventFlow y -> x = y) ∧
      regularCauchyQuotientRefusalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨regularCauchyQuotientRefusalDecode_encode_bhist,
      regularCauchyQuotientRefusal_round_trip,
      by
        intro x y heq
        exact regularCauchyQuotientRefusalToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RegularCauchyQuotientRefusalUp
