import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClusterFilterUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClusterFilterUp : Type where
  | mk (F M T W R E A H C P N : BHist) : ClusterFilterUp
  deriving DecidableEq

def clusterFilterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: clusterFilterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: clusterFilterEncodeBHist h

def clusterFilterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (clusterFilterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (clusterFilterDecodeBHist tail)

private theorem clusterFilter_decode_encode :
    ∀ h : BHist, clusterFilterDecodeBHist (clusterFilterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def clusterFilterFields : ClusterFilterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClusterFilterUp.mk F M T W R E A H C P N => [F, M, T, W, R, E, A, H, C, P, N]

def clusterFilterToEventFlow : ClusterFilterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (clusterFilterFields x).map clusterFilterEncodeBHist

def clusterFilterFromEventFlow : EventFlow → Option ClusterFilterUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | F :: rest0 =>
      match rest0 with
      | [] => none
      | M :: rest1 =>
          match rest1 with
          | [] => none
          | T :: rest2 =>
              match rest2 with
              | [] => none
              | W :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | E :: rest5 =>
                          match rest5 with
                          | [] => none
                          | A :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (ClusterFilterUp.mk
                                                      (clusterFilterDecodeBHist F)
                                                      (clusterFilterDecodeBHist M)
                                                      (clusterFilterDecodeBHist T)
                                                      (clusterFilterDecodeBHist W)
                                                      (clusterFilterDecodeBHist R)
                                                      (clusterFilterDecodeBHist E)
                                                      (clusterFilterDecodeBHist A)
                                                      (clusterFilterDecodeBHist H)
                                                      (clusterFilterDecodeBHist C)
                                                      (clusterFilterDecodeBHist P)
                                                      (clusterFilterDecodeBHist N))
                                              | _ :: _ => none

private theorem clusterFilter_round_trip :
    ∀ x : ClusterFilterUp, clusterFilterFromEventFlow (clusterFilterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F M T W R E A H C P N =>
      change
        some
          (ClusterFilterUp.mk
            (clusterFilterDecodeBHist (clusterFilterEncodeBHist F))
            (clusterFilterDecodeBHist (clusterFilterEncodeBHist M))
            (clusterFilterDecodeBHist (clusterFilterEncodeBHist T))
            (clusterFilterDecodeBHist (clusterFilterEncodeBHist W))
            (clusterFilterDecodeBHist (clusterFilterEncodeBHist R))
            (clusterFilterDecodeBHist (clusterFilterEncodeBHist E))
            (clusterFilterDecodeBHist (clusterFilterEncodeBHist A))
            (clusterFilterDecodeBHist (clusterFilterEncodeBHist H))
            (clusterFilterDecodeBHist (clusterFilterEncodeBHist C))
            (clusterFilterDecodeBHist (clusterFilterEncodeBHist P))
            (clusterFilterDecodeBHist (clusterFilterEncodeBHist N))) =
          some (ClusterFilterUp.mk F M T W R E A H C P N)
      rw [clusterFilter_decode_encode F, clusterFilter_decode_encode M,
        clusterFilter_decode_encode T, clusterFilter_decode_encode W,
        clusterFilter_decode_encode R, clusterFilter_decode_encode E,
        clusterFilter_decode_encode A, clusterFilter_decode_encode H,
        clusterFilter_decode_encode C, clusterFilter_decode_encode P,
        clusterFilter_decode_encode N]

private theorem clusterFilterToEventFlow_injective {x y : ClusterFilterUp} :
    clusterFilterToEventFlow x = clusterFilterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      clusterFilterFromEventFlow (clusterFilterToEventFlow x) =
        clusterFilterFromEventFlow (clusterFilterToEventFlow y) :=
    congrArg clusterFilterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (clusterFilter_round_trip x).symm
      (Eq.trans hread (clusterFilter_round_trip y)))

private theorem clusterFilter_field_faithful :
    ∀ x y : ClusterFilterUp, clusterFilterFields x = clusterFilterFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F₁ M₁ T₁ W₁ R₁ E₁ A₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk F₂ M₂ T₂ W₂ R₂ E₂ A₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance clusterFilterBHistCarrier : BHistCarrier ClusterFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := clusterFilterToEventFlow
  fromEventFlow := clusterFilterFromEventFlow

instance clusterFilterChapterTasteGate : ChapterTasteGate ClusterFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change clusterFilterFromEventFlow (clusterFilterToEventFlow x) = some x
    exact clusterFilter_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (clusterFilterToEventFlow_injective heq)

instance clusterFilterFieldFaithful : FieldFaithful ClusterFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := clusterFilterFields
  field_faithful := clusterFilter_field_faithful

instance clusterFilterNontrivial : Nontrivial ClusterFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClusterFilterUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ClusterFilterUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem ClusterFilterTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ClusterFilterUp) ∧ Nonempty (FieldFaithful ClusterFilterUp) ∧
      Nonempty (Nontrivial ClusterFilterUp) ∧
        (∀ h : BHist, clusterFilterDecodeBHist (clusterFilterEncodeBHist h) = h) ∧
          (∀ x : ClusterFilterUp,
            clusterFilterFromEventFlow (clusterFilterToEventFlow x) = some x) ∧
            clusterFilterEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨clusterFilterChapterTasteGate⟩,
      ⟨clusterFilterFieldFaithful⟩,
      ⟨clusterFilterNontrivial⟩,
      clusterFilter_decode_encode,
      clusterFilter_round_trip,
      rfl⟩

end BEDC.Derived.ClusterFilterUp.TasteGate
