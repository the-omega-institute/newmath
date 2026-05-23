import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CountableChoiceBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CountableChoiceBoundaryUp : Type where
  | mk (Q W R E F L U H C P N : BHist) : CountableChoiceBoundaryUp
  deriving DecidableEq

def countableChoiceBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: countableChoiceBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: countableChoiceBoundaryEncodeBHist h

def countableChoiceBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (countableChoiceBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (countableChoiceBoundaryDecodeBHist tail)

private theorem countableChoiceBoundary_decode_encode_bhist :
    ∀ h : BHist, countableChoiceBoundaryDecodeBHist
      (countableChoiceBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def countableChoiceBoundaryFields : CountableChoiceBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CountableChoiceBoundaryUp.mk Q W R E F L U H C P N => [Q, W, R, E, F, L, U, H, C, P, N]

def countableChoiceBoundaryToEventFlow : CountableChoiceBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map countableChoiceBoundaryEncodeBHist (countableChoiceBoundaryFields x)

def countableChoiceBoundaryFromEventFlow : EventFlow → Option CountableChoiceBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | q :: w :: r :: e :: f :: l :: u :: h :: c :: p :: n :: [] =>
      some
        (CountableChoiceBoundaryUp.mk
          (countableChoiceBoundaryDecodeBHist q)
          (countableChoiceBoundaryDecodeBHist w)
          (countableChoiceBoundaryDecodeBHist r)
          (countableChoiceBoundaryDecodeBHist e)
          (countableChoiceBoundaryDecodeBHist f)
          (countableChoiceBoundaryDecodeBHist l)
          (countableChoiceBoundaryDecodeBHist u)
          (countableChoiceBoundaryDecodeBHist h)
          (countableChoiceBoundaryDecodeBHist c)
          (countableChoiceBoundaryDecodeBHist p)
          (countableChoiceBoundaryDecodeBHist n))
  | _ => none

private theorem countableChoiceBoundary_round_trip :
    ∀ x : CountableChoiceBoundaryUp,
      countableChoiceBoundaryFromEventFlow (countableChoiceBoundaryToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q W R E F L U H C P N =>
      change
        some
          (CountableChoiceBoundaryUp.mk
            (countableChoiceBoundaryDecodeBHist (countableChoiceBoundaryEncodeBHist Q))
            (countableChoiceBoundaryDecodeBHist (countableChoiceBoundaryEncodeBHist W))
            (countableChoiceBoundaryDecodeBHist (countableChoiceBoundaryEncodeBHist R))
            (countableChoiceBoundaryDecodeBHist (countableChoiceBoundaryEncodeBHist E))
            (countableChoiceBoundaryDecodeBHist (countableChoiceBoundaryEncodeBHist F))
            (countableChoiceBoundaryDecodeBHist (countableChoiceBoundaryEncodeBHist L))
            (countableChoiceBoundaryDecodeBHist (countableChoiceBoundaryEncodeBHist U))
            (countableChoiceBoundaryDecodeBHist (countableChoiceBoundaryEncodeBHist H))
            (countableChoiceBoundaryDecodeBHist (countableChoiceBoundaryEncodeBHist C))
            (countableChoiceBoundaryDecodeBHist (countableChoiceBoundaryEncodeBHist P))
            (countableChoiceBoundaryDecodeBHist (countableChoiceBoundaryEncodeBHist N))) =
          some (CountableChoiceBoundaryUp.mk Q W R E F L U H C P N)
      rw [countableChoiceBoundary_decode_encode_bhist Q,
        countableChoiceBoundary_decode_encode_bhist W,
        countableChoiceBoundary_decode_encode_bhist R,
        countableChoiceBoundary_decode_encode_bhist E,
        countableChoiceBoundary_decode_encode_bhist F,
        countableChoiceBoundary_decode_encode_bhist L,
        countableChoiceBoundary_decode_encode_bhist U,
        countableChoiceBoundary_decode_encode_bhist H,
        countableChoiceBoundary_decode_encode_bhist C,
        countableChoiceBoundary_decode_encode_bhist P,
        countableChoiceBoundary_decode_encode_bhist N]

private theorem countableChoiceBoundaryToEventFlow_injective
    {x y : CountableChoiceBoundaryUp} :
    countableChoiceBoundaryToEventFlow x = countableChoiceBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      countableChoiceBoundaryFromEventFlow (countableChoiceBoundaryToEventFlow x) =
        countableChoiceBoundaryFromEventFlow (countableChoiceBoundaryToEventFlow y) :=
    congrArg countableChoiceBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (countableChoiceBoundary_round_trip x).symm
      (Eq.trans hread (countableChoiceBoundary_round_trip y)))

private theorem countableChoiceBoundary_field_faithful :
    ∀ x y : CountableChoiceBoundaryUp, countableChoiceBoundaryFields x =
      countableChoiceBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk Q1 W1 R1 E1 F1 L1 U1 H1 C1 P1 N1 =>
      cases y with
      | mk Q2 W2 R2 E2 F2 L2 U2 H2 C2 P2 N2 =>
          cases h
          rfl

instance countableChoiceBoundaryBHistCarrier : BHistCarrier CountableChoiceBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := countableChoiceBoundaryToEventFlow
  fromEventFlow := countableChoiceBoundaryFromEventFlow

instance countableChoiceBoundaryChapterTasteGate :
    ChapterTasteGate CountableChoiceBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change countableChoiceBoundaryFromEventFlow
      (countableChoiceBoundaryToEventFlow x) = some x
    exact countableChoiceBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (countableChoiceBoundaryToEventFlow_injective heq)

instance countableChoiceBoundaryFieldFaithful : FieldFaithful CountableChoiceBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := countableChoiceBoundaryFields
  field_faithful := countableChoiceBoundary_field_faithful

instance countableChoiceBoundaryNontrivial : Nontrivial CountableChoiceBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CountableChoiceBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CountableChoiceBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CountableChoiceBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  countableChoiceBoundaryChapterTasteGate

end BEDC.Derived.CountableChoiceBoundaryUp
