import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyIntersectionPrincipleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyIntersectionPrincipleUp : Type where
  | mk (D M S R E H C P N : BHist) : CauchyIntersectionPrincipleUp
  deriving DecidableEq

def cauchyIntersectionPrincipleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyIntersectionPrincipleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyIntersectionPrincipleEncodeBHist h

def cauchyIntersectionPrincipleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyIntersectionPrincipleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyIntersectionPrincipleDecodeBHist tail)

private theorem cauchyIntersectionPrinciple_decode_encode_bhist :
    ∀ h : BHist,
      cauchyIntersectionPrincipleDecodeBHist
        (cauchyIntersectionPrincipleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyIntersectionPrincipleFields :
    CauchyIntersectionPrincipleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyIntersectionPrincipleUp.mk D M S R E H C P N => [D, M, S, R, E, H, C, P, N]

def cauchyIntersectionPrincipleToEventFlow :
    CauchyIntersectionPrincipleUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchyIntersectionPrincipleFields x).map cauchyIntersectionPrincipleEncodeBHist

private def cauchyIntersectionPrincipleEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyIntersectionPrincipleEventAtDefault index rest

def cauchyIntersectionPrincipleFromEventFlow
    (ef : EventFlow) : Option CauchyIntersectionPrincipleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyIntersectionPrincipleUp.mk
      (cauchyIntersectionPrincipleDecodeBHist
        (cauchyIntersectionPrincipleEventAtDefault 0 ef))
      (cauchyIntersectionPrincipleDecodeBHist
        (cauchyIntersectionPrincipleEventAtDefault 1 ef))
      (cauchyIntersectionPrincipleDecodeBHist
        (cauchyIntersectionPrincipleEventAtDefault 2 ef))
      (cauchyIntersectionPrincipleDecodeBHist
        (cauchyIntersectionPrincipleEventAtDefault 3 ef))
      (cauchyIntersectionPrincipleDecodeBHist
        (cauchyIntersectionPrincipleEventAtDefault 4 ef))
      (cauchyIntersectionPrincipleDecodeBHist
        (cauchyIntersectionPrincipleEventAtDefault 5 ef))
      (cauchyIntersectionPrincipleDecodeBHist
        (cauchyIntersectionPrincipleEventAtDefault 6 ef))
      (cauchyIntersectionPrincipleDecodeBHist
        (cauchyIntersectionPrincipleEventAtDefault 7 ef))
      (cauchyIntersectionPrincipleDecodeBHist
        (cauchyIntersectionPrincipleEventAtDefault 8 ef)))

private theorem cauchyIntersectionPrinciple_round_trip :
    ∀ x : CauchyIntersectionPrincipleUp,
      cauchyIntersectionPrincipleFromEventFlow
        (cauchyIntersectionPrincipleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D M S R E H C P N =>
      change
        some
          (CauchyIntersectionPrincipleUp.mk
            (cauchyIntersectionPrincipleDecodeBHist
              (cauchyIntersectionPrincipleEncodeBHist D))
            (cauchyIntersectionPrincipleDecodeBHist
              (cauchyIntersectionPrincipleEncodeBHist M))
            (cauchyIntersectionPrincipleDecodeBHist
              (cauchyIntersectionPrincipleEncodeBHist S))
            (cauchyIntersectionPrincipleDecodeBHist
              (cauchyIntersectionPrincipleEncodeBHist R))
            (cauchyIntersectionPrincipleDecodeBHist
              (cauchyIntersectionPrincipleEncodeBHist E))
            (cauchyIntersectionPrincipleDecodeBHist
              (cauchyIntersectionPrincipleEncodeBHist H))
            (cauchyIntersectionPrincipleDecodeBHist
              (cauchyIntersectionPrincipleEncodeBHist C))
            (cauchyIntersectionPrincipleDecodeBHist
              (cauchyIntersectionPrincipleEncodeBHist P))
            (cauchyIntersectionPrincipleDecodeBHist
              (cauchyIntersectionPrincipleEncodeBHist N))) =
          some (CauchyIntersectionPrincipleUp.mk D M S R E H C P N)
      rw [cauchyIntersectionPrinciple_decode_encode_bhist D,
        cauchyIntersectionPrinciple_decode_encode_bhist M,
        cauchyIntersectionPrinciple_decode_encode_bhist S,
        cauchyIntersectionPrinciple_decode_encode_bhist R,
        cauchyIntersectionPrinciple_decode_encode_bhist E,
        cauchyIntersectionPrinciple_decode_encode_bhist H,
        cauchyIntersectionPrinciple_decode_encode_bhist C,
        cauchyIntersectionPrinciple_decode_encode_bhist P,
        cauchyIntersectionPrinciple_decode_encode_bhist N]

private theorem cauchyIntersectionPrincipleToEventFlow_injective
    {x y : CauchyIntersectionPrincipleUp} :
    cauchyIntersectionPrincipleToEventFlow x =
      cauchyIntersectionPrincipleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyIntersectionPrincipleFromEventFlow
          (cauchyIntersectionPrincipleToEventFlow x) =
        cauchyIntersectionPrincipleFromEventFlow
          (cauchyIntersectionPrincipleToEventFlow y) :=
    congrArg cauchyIntersectionPrincipleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyIntersectionPrinciple_round_trip x).symm
      (Eq.trans hread (cauchyIntersectionPrinciple_round_trip y)))

private theorem cauchyIntersectionPrinciple_fields_faithful :
    ∀ x y : CauchyIntersectionPrincipleUp,
      cauchyIntersectionPrincipleFields x =
        cauchyIntersectionPrincipleFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D1 M1 S1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 M2 S2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchyIntersectionPrincipleBHistCarrier :
    BHistCarrier CauchyIntersectionPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyIntersectionPrincipleToEventFlow
  fromEventFlow := cauchyIntersectionPrincipleFromEventFlow

instance cauchyIntersectionPrincipleChapterTasteGate :
    ChapterTasteGate CauchyIntersectionPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyIntersectionPrincipleFromEventFlow
        (cauchyIntersectionPrincipleToEventFlow x) = some x
    exact cauchyIntersectionPrinciple_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyIntersectionPrincipleToEventFlow_injective heq)

instance cauchyIntersectionPrincipleFieldFaithful :
    FieldFaithful CauchyIntersectionPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyIntersectionPrincipleFields
  field_faithful := cauchyIntersectionPrinciple_fields_faithful

theorem CauchyIntersectionPrincipleTasteGate_single_carrier_alignment :
    cauchyIntersectionPrincipleEncodeBHist BHist.Empty = ([] : RawEvent) ∧
      cauchyIntersectionPrincipleEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
        (∀ h : BHist,
          cauchyIntersectionPrincipleDecodeBHist
            (cauchyIntersectionPrincipleEncodeBHist h) = h) ∧
          (∀ x : CauchyIntersectionPrincipleUp,
            cauchyIntersectionPrincipleFromEventFlow
              (cauchyIntersectionPrincipleToEventFlow x) = some x) ∧
            (∀ x y : CauchyIntersectionPrincipleUp,
              cauchyIntersectionPrincipleToEventFlow x =
                cauchyIntersectionPrincipleToEventFlow y → x = y) ∧
              Nonempty (FieldFaithful CauchyIntersectionPrincipleUp) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact cauchyIntersectionPrinciple_decode_encode_bhist
  constructor
  · exact cauchyIntersectionPrinciple_round_trip
  constructor
  · intro x y heq
    exact cauchyIntersectionPrincipleToEventFlow_injective heq
  · exact ⟨cauchyIntersectionPrincipleFieldFaithful⟩

end BEDC.Derived.CauchyIntersectionPrincipleUp
