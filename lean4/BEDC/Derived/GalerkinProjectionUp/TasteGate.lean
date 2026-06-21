import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GalerkinProjectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GalerkinProjectionUp : Type where
  | mk (S H L M V B A b u r O T C P N : BHist) : GalerkinProjectionUp
  deriving DecidableEq

def galerkinProjectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: galerkinProjectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: galerkinProjectionEncodeBHist h

def galerkinProjectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (galerkinProjectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (galerkinProjectionDecodeBHist tail)

private theorem galerkinProjectionDecode_encode_bhist :
    ∀ h : BHist, galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def galerkinProjectionFields : GalerkinProjectionUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | GalerkinProjectionUp.mk S H L M V B A b u r O T C P N =>
      [S, H, L, M, V, B, A, b, u, r, O, T, C, P, N]

def galerkinProjectionToEventFlow : GalerkinProjectionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | GalerkinProjectionUp.mk S H L M V B A b u r O T C P N =>
      [galerkinProjectionEncodeBHist S,
        galerkinProjectionEncodeBHist H,
        galerkinProjectionEncodeBHist L,
        galerkinProjectionEncodeBHist M,
        galerkinProjectionEncodeBHist V,
        galerkinProjectionEncodeBHist B,
        galerkinProjectionEncodeBHist A,
        galerkinProjectionEncodeBHist b,
        galerkinProjectionEncodeBHist u,
        galerkinProjectionEncodeBHist r,
        galerkinProjectionEncodeBHist O,
        galerkinProjectionEncodeBHist T,
        galerkinProjectionEncodeBHist C,
        galerkinProjectionEncodeBHist P,
        galerkinProjectionEncodeBHist N]

private def galerkinProjectionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => galerkinProjectionEventAtDefault index rest

def galerkinProjectionFromEventFlow : EventFlow → Option GalerkinProjectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (GalerkinProjectionUp.mk
        (galerkinProjectionDecodeBHist (galerkinProjectionEventAtDefault 0 ef))
        (galerkinProjectionDecodeBHist (galerkinProjectionEventAtDefault 1 ef))
        (galerkinProjectionDecodeBHist (galerkinProjectionEventAtDefault 2 ef))
        (galerkinProjectionDecodeBHist (galerkinProjectionEventAtDefault 3 ef))
        (galerkinProjectionDecodeBHist (galerkinProjectionEventAtDefault 4 ef))
        (galerkinProjectionDecodeBHist (galerkinProjectionEventAtDefault 5 ef))
        (galerkinProjectionDecodeBHist (galerkinProjectionEventAtDefault 6 ef))
        (galerkinProjectionDecodeBHist (galerkinProjectionEventAtDefault 7 ef))
        (galerkinProjectionDecodeBHist (galerkinProjectionEventAtDefault 8 ef))
        (galerkinProjectionDecodeBHist (galerkinProjectionEventAtDefault 9 ef))
        (galerkinProjectionDecodeBHist (galerkinProjectionEventAtDefault 10 ef))
        (galerkinProjectionDecodeBHist (galerkinProjectionEventAtDefault 11 ef))
        (galerkinProjectionDecodeBHist (galerkinProjectionEventAtDefault 12 ef))
        (galerkinProjectionDecodeBHist (galerkinProjectionEventAtDefault 13 ef))
        (galerkinProjectionDecodeBHist (galerkinProjectionEventAtDefault 14 ef)))

private theorem galerkinProjection_round_trip :
    ∀ x : GalerkinProjectionUp,
      galerkinProjectionFromEventFlow (galerkinProjectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S H L M V B A b u r O T C P N =>
      change
        some
          (GalerkinProjectionUp.mk
            (galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist S))
            (galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist H))
            (galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist L))
            (galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist M))
            (galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist V))
            (galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist B))
            (galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist A))
            (galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist b))
            (galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist u))
            (galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist r))
            (galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist O))
            (galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist T))
            (galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist C))
            (galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist P))
            (galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist N))) =
          some (GalerkinProjectionUp.mk S H L M V B A b u r O T C P N)
      rw [galerkinProjectionDecode_encode_bhist S]
      rw [galerkinProjectionDecode_encode_bhist H]
      rw [galerkinProjectionDecode_encode_bhist L]
      rw [galerkinProjectionDecode_encode_bhist M]
      rw [galerkinProjectionDecode_encode_bhist V]
      rw [galerkinProjectionDecode_encode_bhist B]
      rw [galerkinProjectionDecode_encode_bhist A]
      rw [galerkinProjectionDecode_encode_bhist b]
      rw [galerkinProjectionDecode_encode_bhist u]
      rw [galerkinProjectionDecode_encode_bhist r]
      rw [galerkinProjectionDecode_encode_bhist O]
      rw [galerkinProjectionDecode_encode_bhist T]
      rw [galerkinProjectionDecode_encode_bhist C]
      rw [galerkinProjectionDecode_encode_bhist P]
      rw [galerkinProjectionDecode_encode_bhist N]

private theorem galerkinProjectionToEventFlow_injective {x y : GalerkinProjectionUp} :
    galerkinProjectionToEventFlow x = galerkinProjectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          galerkinProjectionFromEventFlow (galerkinProjectionToEventFlow x) :=
        (galerkinProjection_round_trip x).symm
      _ =
          galerkinProjectionFromEventFlow (galerkinProjectionToEventFlow y) :=
        congrArg galerkinProjectionFromEventFlow hxy
      _ = some y := galerkinProjection_round_trip y
  exact Option.some.inj optionEq

private theorem galerkinProjection_field_faithful :
    ∀ x y : GalerkinProjectionUp, galerkinProjectionFields x = galerkinProjectionFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk S1 H1 L1 M1 V1 B1 A1 b1 u1 r1 O1 T1 C1 P1 N1 =>
      cases y with
      | mk S2 H2 L2 M2 V2 B2 A2 b2 u2 r2 O2 T2 C2 P2 N2 =>
          cases h
          rfl

instance galerkinProjectionBHistCarrier : BHistCarrier GalerkinProjectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := galerkinProjectionToEventFlow
  fromEventFlow := galerkinProjectionFromEventFlow

instance galerkinProjectionChapterTasteGate : ChapterTasteGate GalerkinProjectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change galerkinProjectionFromEventFlow (galerkinProjectionToEventFlow x) = some x
    exact galerkinProjection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (galerkinProjectionToEventFlow_injective heq)

instance galerkinProjectionFieldFaithful : FieldFaithful GalerkinProjectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := galerkinProjectionFields
  field_faithful := galerkinProjection_field_faithful

instance galerkinProjectionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial GalerkinProjectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨GalerkinProjectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      GalerkinProjectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate GalerkinProjectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  galerkinProjectionChapterTasteGate

theorem GalerkinProjectionTasteGate_single_carrier_alignment :
    (∀ h : BHist, galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist h) = h) ∧
      (∀ x : GalerkinProjectionUp,
        galerkinProjectionFromEventFlow (galerkinProjectionToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  · intro x
    cases x with
    | mk S H L M V B A b u r O T C P N =>
        change
          some
            (GalerkinProjectionUp.mk
              (galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist S))
              (galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist H))
              (galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist L))
              (galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist M))
              (galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist V))
              (galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist B))
              (galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist A))
              (galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist b))
              (galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist u))
              (galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist r))
              (galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist O))
              (galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist T))
              (galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist C))
              (galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist P))
              (galerkinProjectionDecodeBHist (galerkinProjectionEncodeBHist N))) =
            some (GalerkinProjectionUp.mk S H L M V B A b u r O T C P N)
        rw [galerkinProjectionDecode_encode_bhist S]
        rw [galerkinProjectionDecode_encode_bhist H]
        rw [galerkinProjectionDecode_encode_bhist L]
        rw [galerkinProjectionDecode_encode_bhist M]
        rw [galerkinProjectionDecode_encode_bhist V]
        rw [galerkinProjectionDecode_encode_bhist B]
        rw [galerkinProjectionDecode_encode_bhist A]
        rw [galerkinProjectionDecode_encode_bhist b]
        rw [galerkinProjectionDecode_encode_bhist u]
        rw [galerkinProjectionDecode_encode_bhist r]
        rw [galerkinProjectionDecode_encode_bhist O]
        rw [galerkinProjectionDecode_encode_bhist T]
        rw [galerkinProjectionDecode_encode_bhist C]
        rw [galerkinProjectionDecode_encode_bhist P]
        rw [galerkinProjectionDecode_encode_bhist N]

end BEDC.Derived.GalerkinProjectionUp
