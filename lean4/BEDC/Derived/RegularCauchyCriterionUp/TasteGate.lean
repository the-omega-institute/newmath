import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyCriterionUp : Type where
  | mk (S R M D Q V A H C P N : BHist) : RegularCauchyCriterionUp
  deriving DecidableEq

def regularCauchyCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyCriterionEncodeBHist h

def regularCauchyCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyCriterionDecodeBHist tail)

private theorem regularCauchyCriterionDecodeEncode :
    ∀ h : BHist,
      regularCauchyCriterionDecodeBHist (regularCauchyCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyCriterionFields : RegularCauchyCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyCriterionUp.mk S R M D Q V A H C P N =>
      [S, R, M, D, Q, V, A, H, C, P, N]

def regularCauchyCriterionToEventFlow : RegularCauchyCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyCriterionFields x).map regularCauchyCriterionEncodeBHist

private def regularCauchyCriterionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyCriterionEventAtDefault index rest

def regularCauchyCriterionFromEventFlow : EventFlow → Option RegularCauchyCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RegularCauchyCriterionUp.mk
        (regularCauchyCriterionDecodeBHist (regularCauchyCriterionEventAtDefault 0 ef))
        (regularCauchyCriterionDecodeBHist (regularCauchyCriterionEventAtDefault 1 ef))
        (regularCauchyCriterionDecodeBHist (regularCauchyCriterionEventAtDefault 2 ef))
        (regularCauchyCriterionDecodeBHist (regularCauchyCriterionEventAtDefault 3 ef))
        (regularCauchyCriterionDecodeBHist (regularCauchyCriterionEventAtDefault 4 ef))
        (regularCauchyCriterionDecodeBHist (regularCauchyCriterionEventAtDefault 5 ef))
        (regularCauchyCriterionDecodeBHist (regularCauchyCriterionEventAtDefault 6 ef))
        (regularCauchyCriterionDecodeBHist (regularCauchyCriterionEventAtDefault 7 ef))
        (regularCauchyCriterionDecodeBHist (regularCauchyCriterionEventAtDefault 8 ef))
        (regularCauchyCriterionDecodeBHist (regularCauchyCriterionEventAtDefault 9 ef))
        (regularCauchyCriterionDecodeBHist (regularCauchyCriterionEventAtDefault 10 ef)))

private theorem regularCauchyCriterionRoundTrip :
    ∀ x : RegularCauchyCriterionUp,
      regularCauchyCriterionFromEventFlow (regularCauchyCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R M D Q V A H C P N =>
      change
        some
          (RegularCauchyCriterionUp.mk
            (regularCauchyCriterionDecodeBHist (regularCauchyCriterionEncodeBHist S))
            (regularCauchyCriterionDecodeBHist (regularCauchyCriterionEncodeBHist R))
            (regularCauchyCriterionDecodeBHist (regularCauchyCriterionEncodeBHist M))
            (regularCauchyCriterionDecodeBHist (regularCauchyCriterionEncodeBHist D))
            (regularCauchyCriterionDecodeBHist (regularCauchyCriterionEncodeBHist Q))
            (regularCauchyCriterionDecodeBHist (regularCauchyCriterionEncodeBHist V))
            (regularCauchyCriterionDecodeBHist (regularCauchyCriterionEncodeBHist A))
            (regularCauchyCriterionDecodeBHist (regularCauchyCriterionEncodeBHist H))
            (regularCauchyCriterionDecodeBHist (regularCauchyCriterionEncodeBHist C))
            (regularCauchyCriterionDecodeBHist (regularCauchyCriterionEncodeBHist P))
            (regularCauchyCriterionDecodeBHist (regularCauchyCriterionEncodeBHist N))) =
          some (RegularCauchyCriterionUp.mk S R M D Q V A H C P N)
      rw [regularCauchyCriterionDecodeEncode S, regularCauchyCriterionDecodeEncode R,
        regularCauchyCriterionDecodeEncode M, regularCauchyCriterionDecodeEncode D,
        regularCauchyCriterionDecodeEncode Q, regularCauchyCriterionDecodeEncode V,
        regularCauchyCriterionDecodeEncode A, regularCauchyCriterionDecodeEncode H,
        regularCauchyCriterionDecodeEncode C, regularCauchyCriterionDecodeEncode P,
        regularCauchyCriterionDecodeEncode N]

private theorem regularCauchyCriterionToEventFlow_injective
    {x y : RegularCauchyCriterionUp} :
    regularCauchyCriterionToEventFlow x = regularCauchyCriterionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyCriterionFromEventFlow (regularCauchyCriterionToEventFlow x) =
        regularCauchyCriterionFromEventFlow (regularCauchyCriterionToEventFlow y) :=
    congrArg regularCauchyCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyCriterionRoundTrip x).symm
      (Eq.trans hread (regularCauchyCriterionRoundTrip y)))

instance regularCauchyCriterionBHistCarrier : BHistCarrier RegularCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyCriterionToEventFlow
  fromEventFlow := regularCauchyCriterionFromEventFlow

instance regularCauchyCriterionChapterTasteGate :
    ChapterTasteGate RegularCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyCriterionFromEventFlow (regularCauchyCriterionToEventFlow x) = some x
    exact regularCauchyCriterionRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyCriterionToEventFlow_injective heq)

theorem RegularCauchyCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyCriterionDecodeBHist (regularCauchyCriterionEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyCriterionUp,
        regularCauchyCriterionFromEventFlow (regularCauchyCriterionToEventFlow x) = some x) ∧
      Nonempty (BHistCarrier RegularCauchyCriterionUp) ∧
        Nonempty (ChapterTasteGate RegularCauchyCriterionUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨regularCauchyCriterionDecodeEncode,
      regularCauchyCriterionRoundTrip,
      ⟨regularCauchyCriterionBHistCarrier⟩,
      ⟨regularCauchyCriterionChapterTasteGate⟩⟩

theorem RegularCauchyCriterionNameCertObligations (S R M D Q V A H C P N : BHist) :
    regularCauchyCriterionFields (RegularCauchyCriterionUp.mk S R M D Q V A H C P N) =
        [S, R, M, D, Q, V, A, H, C, P, N] ∧
      regularCauchyCriterionEncodeBHist BHist.Empty = ([] : List BMark) ∧
        regularCauchyCriterionDecodeBHist (regularCauchyCriterionEncodeBHist S) = S := by
  -- BEDC touchpoint anchor: BHist BMark NameCert
  exact ⟨rfl, rfl, regularCauchyCriterionDecodeEncode S⟩

end BEDC.Derived.RegularCauchyCriterionUp
