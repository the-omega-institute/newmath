import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BanachContractionEndpointUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BanachContractionEndpointUp : Type where
  | mk (M C I R E H K P N : BHist) : BanachContractionEndpointUp
  deriving DecidableEq

def banachContractionEndpointEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: banachContractionEndpointEncodeBHist h
  | BHist.e1 h => BMark.b1 :: banachContractionEndpointEncodeBHist h

def banachContractionEndpointDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (banachContractionEndpointDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (banachContractionEndpointDecodeBHist tail)

private theorem banachContractionEndpoint_decode_encode_bhist :
    forall h : BHist,
      banachContractionEndpointDecodeBHist
        (banachContractionEndpointEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def banachContractionEndpointFields :
    BanachContractionEndpointUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BanachContractionEndpointUp.mk M C I R E H K P N => [M, C, I, R, E, H, K, P, N]

def banachContractionEndpointToEventFlow :
    BanachContractionEndpointUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (banachContractionEndpointFields x).map banachContractionEndpointEncodeBHist

private def banachContractionEndpointEventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => banachContractionEndpointEventAtDefault index rest

def banachContractionEndpointFromEventFlow :
    EventFlow -> Option BanachContractionEndpointUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (BanachContractionEndpointUp.mk
          (banachContractionEndpointDecodeBHist
            (banachContractionEndpointEventAtDefault 0 ef))
          (banachContractionEndpointDecodeBHist
            (banachContractionEndpointEventAtDefault 1 ef))
          (banachContractionEndpointDecodeBHist
            (banachContractionEndpointEventAtDefault 2 ef))
          (banachContractionEndpointDecodeBHist
            (banachContractionEndpointEventAtDefault 3 ef))
          (banachContractionEndpointDecodeBHist
            (banachContractionEndpointEventAtDefault 4 ef))
          (banachContractionEndpointDecodeBHist
            (banachContractionEndpointEventAtDefault 5 ef))
          (banachContractionEndpointDecodeBHist
            (banachContractionEndpointEventAtDefault 6 ef))
          (banachContractionEndpointDecodeBHist
            (banachContractionEndpointEventAtDefault 7 ef))
          (banachContractionEndpointDecodeBHist
            (banachContractionEndpointEventAtDefault 8 ef)))

private theorem banachContractionEndpoint_round_trip :
    forall x : BanachContractionEndpointUp,
      banachContractionEndpointFromEventFlow
        (banachContractionEndpointToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M C I R E H K P N =>
      change
        some
          (BanachContractionEndpointUp.mk
            (banachContractionEndpointDecodeBHist
              (banachContractionEndpointEncodeBHist M))
            (banachContractionEndpointDecodeBHist
              (banachContractionEndpointEncodeBHist C))
            (banachContractionEndpointDecodeBHist
              (banachContractionEndpointEncodeBHist I))
            (banachContractionEndpointDecodeBHist
              (banachContractionEndpointEncodeBHist R))
            (banachContractionEndpointDecodeBHist
              (banachContractionEndpointEncodeBHist E))
            (banachContractionEndpointDecodeBHist
              (banachContractionEndpointEncodeBHist H))
            (banachContractionEndpointDecodeBHist
              (banachContractionEndpointEncodeBHist K))
            (banachContractionEndpointDecodeBHist
              (banachContractionEndpointEncodeBHist P))
            (banachContractionEndpointDecodeBHist
              (banachContractionEndpointEncodeBHist N))) =
          some (BanachContractionEndpointUp.mk M C I R E H K P N)
      rw [banachContractionEndpoint_decode_encode_bhist M,
        banachContractionEndpoint_decode_encode_bhist C,
        banachContractionEndpoint_decode_encode_bhist I,
        banachContractionEndpoint_decode_encode_bhist R,
        banachContractionEndpoint_decode_encode_bhist E,
        banachContractionEndpoint_decode_encode_bhist H,
        banachContractionEndpoint_decode_encode_bhist K,
        banachContractionEndpoint_decode_encode_bhist P,
        banachContractionEndpoint_decode_encode_bhist N]

private theorem banachContractionEndpointToEventFlow_injective
    {x y : BanachContractionEndpointUp} :
    banachContractionEndpointToEventFlow x =
      banachContractionEndpointToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      banachContractionEndpointFromEventFlow
          (banachContractionEndpointToEventFlow x) =
        banachContractionEndpointFromEventFlow
          (banachContractionEndpointToEventFlow y) :=
    congrArg banachContractionEndpointFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (banachContractionEndpoint_round_trip x).symm
      (Eq.trans hread (banachContractionEndpoint_round_trip y)))

private theorem banachContractionEndpoint_fields_faithful :
    forall x y : BanachContractionEndpointUp,
      banachContractionEndpointFields x = banachContractionEndpointFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 C1 I1 R1 E1 H1 K1 P1 N1 =>
      cases y with
      | mk M2 C2 I2 R2 E2 H2 K2 P2 N2 =>
          cases hfields
          rfl

instance banachContractionEndpointBHistCarrier :
    BHistCarrier BanachContractionEndpointUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := banachContractionEndpointToEventFlow
  fromEventFlow := banachContractionEndpointFromEventFlow

instance banachContractionEndpointChapterTasteGate :
    ChapterTasteGate BanachContractionEndpointUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      banachContractionEndpointFromEventFlow
        (banachContractionEndpointToEventFlow x) = some x
    exact banachContractionEndpoint_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (banachContractionEndpointToEventFlow_injective heq)

instance banachContractionEndpointFieldFaithful :
    FieldFaithful BanachContractionEndpointUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := banachContractionEndpointFields
  field_faithful := banachContractionEndpoint_fields_faithful

instance banachContractionEndpointNontrivial :
    Nontrivial BanachContractionEndpointUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BanachContractionEndpointUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BanachContractionEndpointUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BanachContractionEndpointUp :=
  -- BEDC touchpoint anchor: BHist BMark
  banachContractionEndpointChapterTasteGate

theorem BanachContractionEndpointTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        banachContractionEndpointDecodeBHist
          (banachContractionEndpointEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BanachContractionEndpointUp) ∧
        Nonempty (ChapterTasteGate BanachContractionEndpointUp) ∧
          Nonempty (FieldFaithful BanachContractionEndpointUp) ∧
            Nonempty (Nontrivial BanachContractionEndpointUp) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate Nontrivial
  exact
    ⟨banachContractionEndpoint_decode_encode_bhist,
      ⟨banachContractionEndpointBHistCarrier⟩,
      ⟨banachContractionEndpointChapterTasteGate⟩,
      ⟨banachContractionEndpointFieldFaithful⟩,
      ⟨banachContractionEndpointNontrivial⟩⟩

end BEDC.Derived.BanachContractionEndpointUp
