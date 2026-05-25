import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HyersUlamStabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HyersUlamStabilityUp : Type where
  | mk (A W L M R H C P N : BHist) : HyersUlamStabilityUp
  deriving DecidableEq

def hyersUlamStabilityEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hyersUlamStabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hyersUlamStabilityEncodeBHist h

def hyersUlamStabilityDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hyersUlamStabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hyersUlamStabilityDecodeBHist tail)

private theorem HyersUlamStabilityUpTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      hyersUlamStabilityDecodeBHist (hyersUlamStabilityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hyersUlamStabilityFields : HyersUlamStabilityUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HyersUlamStabilityUp.mk A W L M R H C P N => [A, W, L, M, R, H, C, P, N]

def hyersUlamStabilityToEventFlow : HyersUlamStabilityUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hyersUlamStabilityFields x).map hyersUlamStabilityEncodeBHist

def hyersUlamStabilityFromEventFlow : EventFlow -> Option HyersUlamStabilityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | A :: rest0 =>
      match rest0 with
      | [] => none
      | W :: rest1 =>
          match rest1 with
          | [] => none
          | L :: rest2 =>
              match rest2 with
              | [] => none
              | M :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | C :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (HyersUlamStabilityUp.mk
                                              (hyersUlamStabilityDecodeBHist A)
                                              (hyersUlamStabilityDecodeBHist W)
                                              (hyersUlamStabilityDecodeBHist L)
                                              (hyersUlamStabilityDecodeBHist M)
                                              (hyersUlamStabilityDecodeBHist R)
                                              (hyersUlamStabilityDecodeBHist H)
                                              (hyersUlamStabilityDecodeBHist C)
                                              (hyersUlamStabilityDecodeBHist P)
                                              (hyersUlamStabilityDecodeBHist N))
                                      | _ :: _ => none

private theorem HyersUlamStabilityUpTasteGate_single_carrier_alignment_round_trip :
    forall x : HyersUlamStabilityUp,
      hyersUlamStabilityFromEventFlow (hyersUlamStabilityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A W L M R H C P N =>
      change
        some
          (HyersUlamStabilityUp.mk
            (hyersUlamStabilityDecodeBHist (hyersUlamStabilityEncodeBHist A))
            (hyersUlamStabilityDecodeBHist (hyersUlamStabilityEncodeBHist W))
            (hyersUlamStabilityDecodeBHist (hyersUlamStabilityEncodeBHist L))
            (hyersUlamStabilityDecodeBHist (hyersUlamStabilityEncodeBHist M))
            (hyersUlamStabilityDecodeBHist (hyersUlamStabilityEncodeBHist R))
            (hyersUlamStabilityDecodeBHist (hyersUlamStabilityEncodeBHist H))
            (hyersUlamStabilityDecodeBHist (hyersUlamStabilityEncodeBHist C))
            (hyersUlamStabilityDecodeBHist (hyersUlamStabilityEncodeBHist P))
            (hyersUlamStabilityDecodeBHist (hyersUlamStabilityEncodeBHist N))) =
          some (HyersUlamStabilityUp.mk A W L M R H C P N)
      rw [HyersUlamStabilityUpTasteGate_single_carrier_alignment_decode_encode A,
        HyersUlamStabilityUpTasteGate_single_carrier_alignment_decode_encode W,
        HyersUlamStabilityUpTasteGate_single_carrier_alignment_decode_encode L,
        HyersUlamStabilityUpTasteGate_single_carrier_alignment_decode_encode M,
        HyersUlamStabilityUpTasteGate_single_carrier_alignment_decode_encode R,
        HyersUlamStabilityUpTasteGate_single_carrier_alignment_decode_encode H,
        HyersUlamStabilityUpTasteGate_single_carrier_alignment_decode_encode C,
        HyersUlamStabilityUpTasteGate_single_carrier_alignment_decode_encode P,
        HyersUlamStabilityUpTasteGate_single_carrier_alignment_decode_encode N]

private theorem HyersUlamStabilityUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HyersUlamStabilityUp} :
    hyersUlamStabilityToEventFlow x = hyersUlamStabilityToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hyersUlamStabilityFromEventFlow (hyersUlamStabilityToEventFlow x) =
        hyersUlamStabilityFromEventFlow (hyersUlamStabilityToEventFlow y) :=
    congrArg hyersUlamStabilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HyersUlamStabilityUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HyersUlamStabilityUpTasteGate_single_carrier_alignment_round_trip y)))

private theorem HyersUlamStabilityUpTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : HyersUlamStabilityUp,
      hyersUlamStabilityFields x = hyersUlamStabilityFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 W1 L1 M1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk A2 W2 L2 M2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance hyersUlamStabilityBHistCarrier : BHistCarrier HyersUlamStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hyersUlamStabilityToEventFlow
  fromEventFlow := hyersUlamStabilityFromEventFlow

instance hyersUlamStabilityChapterTasteGate : ChapterTasteGate HyersUlamStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hyersUlamStabilityFromEventFlow (hyersUlamStabilityToEventFlow x) = some x
    exact HyersUlamStabilityUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HyersUlamStabilityUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance hyersUlamStabilityFieldFaithful : FieldFaithful HyersUlamStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hyersUlamStabilityFields
  field_faithful := HyersUlamStabilityUpTasteGate_single_carrier_alignment_fields_faithful

instance hyersUlamStabilityNontrivial :
    BEDC.Meta.TasteGate.Nontrivial HyersUlamStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HyersUlamStabilityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HyersUlamStabilityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def hyersUlamStabilityTasteGate : ChapterTasteGate HyersUlamStabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hyersUlamStabilityChapterTasteGate

theorem HyersUlamStabilityUpTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate HyersUlamStabilityUp) ∧
      Nonempty (FieldFaithful HyersUlamStabilityUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial HyersUlamStabilityUp) ∧
          (∀ h : BHist,
            hyersUlamStabilityDecodeBHist (hyersUlamStabilityEncodeBHist h) = h) ∧
            (∀ x : HyersUlamStabilityUp,
              hyersUlamStabilityFromEventFlow (hyersUlamStabilityToEventFlow x) = some x) ∧
              (∀ x y : HyersUlamStabilityUp,
                hyersUlamStabilityToEventFlow x = hyersUlamStabilityToEventFlow y -> x = y) ∧
                hyersUlamStabilityEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨hyersUlamStabilityChapterTasteGate⟩
  · constructor
    · exact ⟨hyersUlamStabilityFieldFaithful⟩
    · constructor
      · exact ⟨hyersUlamStabilityNontrivial⟩
      · constructor
        · exact HyersUlamStabilityUpTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact HyersUlamStabilityUpTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact HyersUlamStabilityUpTasteGate_single_carrier_alignment_toEventFlow_injective heq
            · rfl

end BEDC.Derived.HyersUlamStabilityUp
