import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RiemannStieltjesIntegrationPartsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RiemannStieltjesIntegrationPartsUp : Type where
  | mk (F G V R S D B E H C P N : BHist) : RiemannStieltjesIntegrationPartsUp
  deriving DecidableEq

def riemannStieltjesIntegrationPartsEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: riemannStieltjesIntegrationPartsEncodeBHist h
  | BHist.e1 h => BMark.b1 :: riemannStieltjesIntegrationPartsEncodeBHist h

def riemannStieltjesIntegrationPartsDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (riemannStieltjesIntegrationPartsDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (riemannStieltjesIntegrationPartsDecodeBHist tail)

private theorem riemannStieltjesIntegrationParts_decode_encode_bhist :
    ∀ h : BHist,
      riemannStieltjesIntegrationPartsDecodeBHist
        (riemannStieltjesIntegrationPartsEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def riemannStieltjesIntegrationPartsFields :
    RiemannStieltjesIntegrationPartsUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RiemannStieltjesIntegrationPartsUp.mk F G V R S D B E H C P N =>
      [F, G, V, R, S, D, B, E, H, C, P, N]

def riemannStieltjesIntegrationPartsToEventFlow :
    RiemannStieltjesIntegrationPartsUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (riemannStieltjesIntegrationPartsFields x).map
    riemannStieltjesIntegrationPartsEncodeBHist

private def riemannStieltjesIntegrationPartsEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => riemannStieltjesIntegrationPartsEventAtDefault index rest

def riemannStieltjesIntegrationPartsFromEventFlow
    (ef : EventFlow) : Option RiemannStieltjesIntegrationPartsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RiemannStieltjesIntegrationPartsUp.mk
      (riemannStieltjesIntegrationPartsDecodeBHist
        (riemannStieltjesIntegrationPartsEventAtDefault 0 ef))
      (riemannStieltjesIntegrationPartsDecodeBHist
        (riemannStieltjesIntegrationPartsEventAtDefault 1 ef))
      (riemannStieltjesIntegrationPartsDecodeBHist
        (riemannStieltjesIntegrationPartsEventAtDefault 2 ef))
      (riemannStieltjesIntegrationPartsDecodeBHist
        (riemannStieltjesIntegrationPartsEventAtDefault 3 ef))
      (riemannStieltjesIntegrationPartsDecodeBHist
        (riemannStieltjesIntegrationPartsEventAtDefault 4 ef))
      (riemannStieltjesIntegrationPartsDecodeBHist
        (riemannStieltjesIntegrationPartsEventAtDefault 5 ef))
      (riemannStieltjesIntegrationPartsDecodeBHist
        (riemannStieltjesIntegrationPartsEventAtDefault 6 ef))
      (riemannStieltjesIntegrationPartsDecodeBHist
        (riemannStieltjesIntegrationPartsEventAtDefault 7 ef))
      (riemannStieltjesIntegrationPartsDecodeBHist
        (riemannStieltjesIntegrationPartsEventAtDefault 8 ef))
      (riemannStieltjesIntegrationPartsDecodeBHist
        (riemannStieltjesIntegrationPartsEventAtDefault 9 ef))
      (riemannStieltjesIntegrationPartsDecodeBHist
        (riemannStieltjesIntegrationPartsEventAtDefault 10 ef))
      (riemannStieltjesIntegrationPartsDecodeBHist
        (riemannStieltjesIntegrationPartsEventAtDefault 11 ef)))

private theorem riemannStieltjesIntegrationParts_round_trip :
    ∀ x : RiemannStieltjesIntegrationPartsUp,
      riemannStieltjesIntegrationPartsFromEventFlow
        (riemannStieltjesIntegrationPartsToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F G V R S D B E H C P N =>
      change
        some
          (RiemannStieltjesIntegrationPartsUp.mk
            (riemannStieltjesIntegrationPartsDecodeBHist
              (riemannStieltjesIntegrationPartsEncodeBHist F))
            (riemannStieltjesIntegrationPartsDecodeBHist
              (riemannStieltjesIntegrationPartsEncodeBHist G))
            (riemannStieltjesIntegrationPartsDecodeBHist
              (riemannStieltjesIntegrationPartsEncodeBHist V))
            (riemannStieltjesIntegrationPartsDecodeBHist
              (riemannStieltjesIntegrationPartsEncodeBHist R))
            (riemannStieltjesIntegrationPartsDecodeBHist
              (riemannStieltjesIntegrationPartsEncodeBHist S))
            (riemannStieltjesIntegrationPartsDecodeBHist
              (riemannStieltjesIntegrationPartsEncodeBHist D))
            (riemannStieltjesIntegrationPartsDecodeBHist
              (riemannStieltjesIntegrationPartsEncodeBHist B))
            (riemannStieltjesIntegrationPartsDecodeBHist
              (riemannStieltjesIntegrationPartsEncodeBHist E))
            (riemannStieltjesIntegrationPartsDecodeBHist
              (riemannStieltjesIntegrationPartsEncodeBHist H))
            (riemannStieltjesIntegrationPartsDecodeBHist
              (riemannStieltjesIntegrationPartsEncodeBHist C))
            (riemannStieltjesIntegrationPartsDecodeBHist
              (riemannStieltjesIntegrationPartsEncodeBHist P))
            (riemannStieltjesIntegrationPartsDecodeBHist
              (riemannStieltjesIntegrationPartsEncodeBHist N))) =
          some (RiemannStieltjesIntegrationPartsUp.mk F G V R S D B E H C P N)
      rw [riemannStieltjesIntegrationParts_decode_encode_bhist F,
        riemannStieltjesIntegrationParts_decode_encode_bhist G,
        riemannStieltjesIntegrationParts_decode_encode_bhist V,
        riemannStieltjesIntegrationParts_decode_encode_bhist R,
        riemannStieltjesIntegrationParts_decode_encode_bhist S,
        riemannStieltjesIntegrationParts_decode_encode_bhist D,
        riemannStieltjesIntegrationParts_decode_encode_bhist B,
        riemannStieltjesIntegrationParts_decode_encode_bhist E,
        riemannStieltjesIntegrationParts_decode_encode_bhist H,
        riemannStieltjesIntegrationParts_decode_encode_bhist C,
        riemannStieltjesIntegrationParts_decode_encode_bhist P,
        riemannStieltjesIntegrationParts_decode_encode_bhist N]

private theorem riemannStieltjesIntegrationPartsToEventFlow_injective
    {x y : RiemannStieltjesIntegrationPartsUp} :
    riemannStieltjesIntegrationPartsToEventFlow x =
      riemannStieltjesIntegrationPartsToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          riemannStieltjesIntegrationPartsFromEventFlow
            (riemannStieltjesIntegrationPartsToEventFlow x) :=
        (riemannStieltjesIntegrationParts_round_trip x).symm
      _ =
          riemannStieltjesIntegrationPartsFromEventFlow
            (riemannStieltjesIntegrationPartsToEventFlow y) :=
        congrArg riemannStieltjesIntegrationPartsFromEventFlow hxy
      _ = some y := riemannStieltjesIntegrationParts_round_trip y
  exact Option.some.inj optionEq

private theorem riemannStieltjesIntegrationParts_fields_faithful :
    ∀ x y : RiemannStieltjesIntegrationPartsUp,
      riemannStieltjesIntegrationPartsFields x =
        riemannStieltjesIntegrationPartsFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 G1 V1 R1 S1 D1 B1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk F2 G2 V2 R2 S2 D2 B2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance riemannStieltjesIntegrationPartsBHistCarrier :
    BHistCarrier RiemannStieltjesIntegrationPartsUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := riemannStieltjesIntegrationPartsToEventFlow
  fromEventFlow := riemannStieltjesIntegrationPartsFromEventFlow

instance riemannStieltjesIntegrationPartsChapterTasteGate :
    ChapterTasteGate RiemannStieltjesIntegrationPartsUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      riemannStieltjesIntegrationPartsFromEventFlow
        (riemannStieltjesIntegrationPartsToEventFlow x) = some x
    exact riemannStieltjesIntegrationParts_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (riemannStieltjesIntegrationPartsToEventFlow_injective heq)

instance riemannStieltjesIntegrationPartsFieldFaithful :
    FieldFaithful RiemannStieltjesIntegrationPartsUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := riemannStieltjesIntegrationPartsFields
  field_faithful := riemannStieltjesIntegrationParts_fields_faithful

instance riemannStieltjesIntegrationPartsNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RiemannStieltjesIntegrationPartsUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RiemannStieltjesIntegrationPartsUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      RiemannStieltjesIntegrationPartsUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RiemannStieltjesIntegrationPartsTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RiemannStieltjesIntegrationPartsUp) ∧
      Nonempty (FieldFaithful RiemannStieltjesIntegrationPartsUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RiemannStieltjesIntegrationPartsUp) ∧
          (∀ h : BHist,
            riemannStieltjesIntegrationPartsDecodeBHist
              (riemannStieltjesIntegrationPartsEncodeBHist h) = h) ∧
            (∀ x : RiemannStieltjesIntegrationPartsUp,
              riemannStieltjesIntegrationPartsFromEventFlow
                (riemannStieltjesIntegrationPartsToEventFlow x) = some x) ∧
              (∀ x y : RiemannStieltjesIntegrationPartsUp,
                riemannStieltjesIntegrationPartsToEventFlow x =
                  riemannStieltjesIntegrationPartsToEventFlow y → x = y) ∧
                riemannStieltjesIntegrationPartsEncodeBHist BHist.Empty =
                  ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨riemannStieltjesIntegrationPartsChapterTasteGate⟩,
      ⟨riemannStieltjesIntegrationPartsFieldFaithful⟩,
      ⟨riemannStieltjesIntegrationPartsNontrivial⟩,
      riemannStieltjesIntegrationParts_decode_encode_bhist,
      riemannStieltjesIntegrationParts_round_trip,
      (by
        intro x y heq
        exact riemannStieltjesIntegrationPartsToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RiemannStieltjesIntegrationPartsUp
