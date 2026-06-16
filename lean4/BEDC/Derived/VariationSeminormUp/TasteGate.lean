import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.VariationSeminormUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive VariationSeminormUp : Type where
  | mk (B F J T R Q A L H C P N : BHist) : VariationSeminormUp
  deriving DecidableEq

def variationSeminormEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: variationSeminormEncodeBHist h
  | BHist.e1 h => BMark.b1 :: variationSeminormEncodeBHist h

def variationSeminormDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (variationSeminormDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (variationSeminormDecodeBHist tail)

private theorem VariationSeminormTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, variationSeminormDecodeBHist (variationSeminormEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def variationSeminormFields : VariationSeminormUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | VariationSeminormUp.mk B F J T R Q A L H C P N => [B, F, J, T, R, Q, A, L, H, C, P, N]

def variationSeminormToEventFlow : VariationSeminormUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (variationSeminormFields x).map variationSeminormEncodeBHist

private def variationSeminormEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => variationSeminormEventAt index rest

def variationSeminormFromEventFlow : EventFlow → Option VariationSeminormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (VariationSeminormUp.mk
        (variationSeminormDecodeBHist (variationSeminormEventAt 0 ef))
        (variationSeminormDecodeBHist (variationSeminormEventAt 1 ef))
        (variationSeminormDecodeBHist (variationSeminormEventAt 2 ef))
        (variationSeminormDecodeBHist (variationSeminormEventAt 3 ef))
        (variationSeminormDecodeBHist (variationSeminormEventAt 4 ef))
        (variationSeminormDecodeBHist (variationSeminormEventAt 5 ef))
        (variationSeminormDecodeBHist (variationSeminormEventAt 6 ef))
        (variationSeminormDecodeBHist (variationSeminormEventAt 7 ef))
        (variationSeminormDecodeBHist (variationSeminormEventAt 8 ef))
        (variationSeminormDecodeBHist (variationSeminormEventAt 9 ef))
        (variationSeminormDecodeBHist (variationSeminormEventAt 10 ef))
        (variationSeminormDecodeBHist (variationSeminormEventAt 11 ef)))

private theorem variationSeminorm_round_trip :
    ∀ x : VariationSeminormUp,
      variationSeminormFromEventFlow (variationSeminormToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B F J T R Q A L H C P N =>
      change
        some
          (VariationSeminormUp.mk
            (variationSeminormDecodeBHist (variationSeminormEncodeBHist B))
            (variationSeminormDecodeBHist (variationSeminormEncodeBHist F))
            (variationSeminormDecodeBHist (variationSeminormEncodeBHist J))
            (variationSeminormDecodeBHist (variationSeminormEncodeBHist T))
            (variationSeminormDecodeBHist (variationSeminormEncodeBHist R))
            (variationSeminormDecodeBHist (variationSeminormEncodeBHist Q))
            (variationSeminormDecodeBHist (variationSeminormEncodeBHist A))
            (variationSeminormDecodeBHist (variationSeminormEncodeBHist L))
            (variationSeminormDecodeBHist (variationSeminormEncodeBHist H))
            (variationSeminormDecodeBHist (variationSeminormEncodeBHist C))
            (variationSeminormDecodeBHist (variationSeminormEncodeBHist P))
            (variationSeminormDecodeBHist (variationSeminormEncodeBHist N))) =
          some (VariationSeminormUp.mk B F J T R Q A L H C P N)
      rw [VariationSeminormTasteGate_single_carrier_alignment_decode_encode B,
        VariationSeminormTasteGate_single_carrier_alignment_decode_encode F,
        VariationSeminormTasteGate_single_carrier_alignment_decode_encode J,
        VariationSeminormTasteGate_single_carrier_alignment_decode_encode T,
        VariationSeminormTasteGate_single_carrier_alignment_decode_encode R,
        VariationSeminormTasteGate_single_carrier_alignment_decode_encode Q,
        VariationSeminormTasteGate_single_carrier_alignment_decode_encode A,
        VariationSeminormTasteGate_single_carrier_alignment_decode_encode L,
        VariationSeminormTasteGate_single_carrier_alignment_decode_encode H,
        VariationSeminormTasteGate_single_carrier_alignment_decode_encode C,
        VariationSeminormTasteGate_single_carrier_alignment_decode_encode P,
        VariationSeminormTasteGate_single_carrier_alignment_decode_encode N]

private theorem variationSeminormToEventFlow_injective {x y : VariationSeminormUp} :
    variationSeminormToEventFlow x = variationSeminormToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      variationSeminormFromEventFlow (variationSeminormToEventFlow x) =
        variationSeminormFromEventFlow (variationSeminormToEventFlow y) :=
    congrArg variationSeminormFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (variationSeminorm_round_trip x).symm
      (Eq.trans hread (variationSeminorm_round_trip y)))

private theorem variationSeminorm_field_faithful :
    ∀ x y : VariationSeminormUp, variationSeminormFields x = variationSeminormFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 F1 J1 T1 R1 Q1 A1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk B2 F2 J2 T2 R2 Q2 A2 L2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance variationSeminormBHistCarrier : BHistCarrier VariationSeminormUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := variationSeminormToEventFlow
  fromEventFlow := variationSeminormFromEventFlow

instance variationSeminormChapterTasteGate : ChapterTasteGate VariationSeminormUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change variationSeminormFromEventFlow (variationSeminormToEventFlow x) = some x
    exact variationSeminorm_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (variationSeminormToEventFlow_injective heq)

instance variationSeminormFieldFaithful : FieldFaithful VariationSeminormUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := variationSeminormFields
  field_faithful := variationSeminorm_field_faithful

instance variationSeminormNontrivial : Nontrivial VariationSeminormUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨VariationSeminormUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      VariationSeminormUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem VariationSeminormTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate VariationSeminormUp) ∧
      Nonempty (FieldFaithful VariationSeminormUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial VariationSeminormUp) ∧
          (∀ h : BHist, variationSeminormDecodeBHist (variationSeminormEncodeBHist h) = h) ∧
            (∀ x : VariationSeminormUp,
              variationSeminormFromEventFlow (variationSeminormToEventFlow x) = some x) ∧
              (∀ x y : VariationSeminormUp,
                variationSeminormToEventFlow x = variationSeminormToEventFlow y → x = y) ∧
                variationSeminormEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact ⟨variationSeminormChapterTasteGate⟩
  constructor
  · exact ⟨variationSeminormFieldFaithful⟩
  constructor
  · exact ⟨variationSeminormNontrivial⟩
  constructor
  · exact VariationSeminormTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact variationSeminorm_round_trip
  constructor
  · intro x y heq
    exact variationSeminormToEventFlow_injective heq
  · rfl

end BEDC.Derived.VariationSeminormUp
