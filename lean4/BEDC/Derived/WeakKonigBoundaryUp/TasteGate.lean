import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.WeakKonigBoundaryUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive WeakKonigBoundaryUp : Type where
  | mk (K A F S Q R O H C P N : BHist) : WeakKonigBoundaryUp
  deriving DecidableEq

def weakKonigBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: weakKonigBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: weakKonigBoundaryEncodeBHist h

def weakKonigBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (weakKonigBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (weakKonigBoundaryDecodeBHist tail)

private theorem weakKonigBoundaryDecode_encode_bhist :
    ∀ h : BHist, weakKonigBoundaryDecodeBHist (weakKonigBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def weakKonigBoundaryFields : WeakKonigBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | WeakKonigBoundaryUp.mk K A F S Q R O H C P N => [K, A, F, S, Q, R, O, H, C, P, N]

def weakKonigBoundaryToEventFlow : WeakKonigBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (weakKonigBoundaryFields x).map weakKonigBoundaryEncodeBHist

def weakKonigBoundaryFromEventFlow : EventFlow → Option WeakKonigBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | K :: A :: F :: S :: Q :: R :: O :: H :: C :: P :: N :: [] =>
      some
        (WeakKonigBoundaryUp.mk
          (weakKonigBoundaryDecodeBHist K)
          (weakKonigBoundaryDecodeBHist A)
          (weakKonigBoundaryDecodeBHist F)
          (weakKonigBoundaryDecodeBHist S)
          (weakKonigBoundaryDecodeBHist Q)
          (weakKonigBoundaryDecodeBHist R)
          (weakKonigBoundaryDecodeBHist O)
          (weakKonigBoundaryDecodeBHist H)
          (weakKonigBoundaryDecodeBHist C)
          (weakKonigBoundaryDecodeBHist P)
          (weakKonigBoundaryDecodeBHist N))
  | _ => none

private theorem weakKonigBoundary_round_trip :
    ∀ x : WeakKonigBoundaryUp,
      weakKonigBoundaryFromEventFlow (weakKonigBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K A F S Q R O H C P N =>
      change
        some
          (WeakKonigBoundaryUp.mk
            (weakKonigBoundaryDecodeBHist (weakKonigBoundaryEncodeBHist K))
            (weakKonigBoundaryDecodeBHist (weakKonigBoundaryEncodeBHist A))
            (weakKonigBoundaryDecodeBHist (weakKonigBoundaryEncodeBHist F))
            (weakKonigBoundaryDecodeBHist (weakKonigBoundaryEncodeBHist S))
            (weakKonigBoundaryDecodeBHist (weakKonigBoundaryEncodeBHist Q))
            (weakKonigBoundaryDecodeBHist (weakKonigBoundaryEncodeBHist R))
            (weakKonigBoundaryDecodeBHist (weakKonigBoundaryEncodeBHist O))
            (weakKonigBoundaryDecodeBHist (weakKonigBoundaryEncodeBHist H))
            (weakKonigBoundaryDecodeBHist (weakKonigBoundaryEncodeBHist C))
            (weakKonigBoundaryDecodeBHist (weakKonigBoundaryEncodeBHist P))
            (weakKonigBoundaryDecodeBHist (weakKonigBoundaryEncodeBHist N))) =
          some (WeakKonigBoundaryUp.mk K A F S Q R O H C P N)
      rw [weakKonigBoundaryDecode_encode_bhist K, weakKonigBoundaryDecode_encode_bhist A,
        weakKonigBoundaryDecode_encode_bhist F, weakKonigBoundaryDecode_encode_bhist S,
        weakKonigBoundaryDecode_encode_bhist Q, weakKonigBoundaryDecode_encode_bhist R,
        weakKonigBoundaryDecode_encode_bhist O, weakKonigBoundaryDecode_encode_bhist H,
        weakKonigBoundaryDecode_encode_bhist C, weakKonigBoundaryDecode_encode_bhist P,
        weakKonigBoundaryDecode_encode_bhist N]

private theorem weakKonigBoundaryToEventFlow_injective {x y : WeakKonigBoundaryUp} :
    weakKonigBoundaryToEventFlow x = weakKonigBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      weakKonigBoundaryFromEventFlow (weakKonigBoundaryToEventFlow x) =
        weakKonigBoundaryFromEventFlow (weakKonigBoundaryToEventFlow y) :=
    congrArg weakKonigBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (weakKonigBoundary_round_trip x).symm
      (Eq.trans hread (weakKonigBoundary_round_trip y)))

instance weakKonigBoundaryBHistCarrier : BHistCarrier WeakKonigBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := weakKonigBoundaryToEventFlow
  fromEventFlow := weakKonigBoundaryFromEventFlow

instance weakKonigBoundaryChapterTasteGate : ChapterTasteGate WeakKonigBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x => by
    change weakKonigBoundaryFromEventFlow (weakKonigBoundaryToEventFlow x) = some x
    exact weakKonigBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (weakKonigBoundaryToEventFlow_injective heq)

theorem WeakKonigBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist, weakKonigBoundaryDecodeBHist (weakKonigBoundaryEncodeBHist h) = h) ∧
      (∀ x : WeakKonigBoundaryUp,
        weakKonigBoundaryFromEventFlow (weakKonigBoundaryToEventFlow x) = some x) ∧
      (∀ x y : WeakKonigBoundaryUp,
        weakKonigBoundaryToEventFlow x = weakKonigBoundaryToEventFlow y → x = y) ∧
      weakKonigBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact weakKonigBoundaryDecode_encode_bhist
  · constructor
    · exact weakKonigBoundary_round_trip
    · constructor
      · intro x y
        exact weakKonigBoundaryToEventFlow_injective
      · rfl

end BEDC.Derived.WeakKonigBoundaryUp.TasteGate
