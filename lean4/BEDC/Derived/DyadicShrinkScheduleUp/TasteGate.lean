import BEDC.Derived.DyadicShrinkScheduleUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicShrinkScheduleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def dyadicShrinkScheduleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicShrinkScheduleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicShrinkScheduleEncodeBHist h

def dyadicShrinkScheduleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicShrinkScheduleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicShrinkScheduleDecodeBHist tail)

private theorem DyadicShrinkScheduleTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      dyadicShrinkScheduleDecodeBHist (dyadicShrinkScheduleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicShrinkScheduleFields : DyadicShrinkScheduleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicShrinkScheduleUp.mk k k' D W R E H C P N => [k, k', D, W, R, E, H, C, P, N]

def dyadicShrinkScheduleToEventFlow : DyadicShrinkScheduleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicShrinkScheduleFields x).map dyadicShrinkScheduleEncodeBHist

def dyadicShrinkScheduleFromEventFlow : EventFlow → Option DyadicShrinkScheduleUp
  -- BEDC touchpoint anchor: BHist BMark
  | k :: restK =>
      match restK with
      | k' :: restK' =>
          match restK' with
          | D :: restD =>
              match restD with
              | W :: restW =>
                  match restW with
                  | R :: restR =>
                      match restR with
                      | E :: restE =>
                          match restE with
                          | H :: restH =>
                              match restH with
                              | C :: restC =>
                                  match restC with
                                  | P :: restP =>
                                      match restP with
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (DyadicShrinkScheduleUp.mk
                                                  (dyadicShrinkScheduleDecodeBHist k)
                                                  (dyadicShrinkScheduleDecodeBHist k')
                                                  (dyadicShrinkScheduleDecodeBHist D)
                                                  (dyadicShrinkScheduleDecodeBHist W)
                                                  (dyadicShrinkScheduleDecodeBHist R)
                                                  (dyadicShrinkScheduleDecodeBHist E)
                                                  (dyadicShrinkScheduleDecodeBHist H)
                                                  (dyadicShrinkScheduleDecodeBHist C)
                                                  (dyadicShrinkScheduleDecodeBHist P)
                                                  (dyadicShrinkScheduleDecodeBHist N))
                                          | _ :: _ => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem dyadicShrinkSchedule_mk_congr
    {k₁ k₂ k₁' k₂' D₁ D₂ W₁ W₂ R₁ R₂ E₁ E₂ H₁ H₂ C₁ C₂ P₁ P₂ N₁ N₂ : BHist}
    (hk : k₂ = k₁) (hk' : k₂' = k₁') (hD : D₂ = D₁) (hW : W₂ = W₁)
    (hR : R₂ = R₁) (hE : E₂ = E₁) (hH : H₂ = H₁) (hC : C₂ = C₁)
    (hP : P₂ = P₁) (hN : N₂ = N₁) :
    DyadicShrinkScheduleUp.mk k₂ k₂' D₂ W₂ R₂ E₂ H₂ C₂ P₂ N₂ =
      DyadicShrinkScheduleUp.mk k₁ k₁' D₁ W₁ R₁ E₁ H₁ C₁ P₁ N₁ := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hk
  cases hk'
  cases hD
  cases hW
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem DyadicShrinkScheduleTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DyadicShrinkScheduleUp,
      dyadicShrinkScheduleFromEventFlow (dyadicShrinkScheduleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk k k' D W R E H C P N =>
      exact
        congrArg some
          (dyadicShrinkSchedule_mk_congr
            (DyadicShrinkScheduleTasteGate_single_carrier_alignment_decode k)
            (DyadicShrinkScheduleTasteGate_single_carrier_alignment_decode k')
            (DyadicShrinkScheduleTasteGate_single_carrier_alignment_decode D)
            (DyadicShrinkScheduleTasteGate_single_carrier_alignment_decode W)
            (DyadicShrinkScheduleTasteGate_single_carrier_alignment_decode R)
            (DyadicShrinkScheduleTasteGate_single_carrier_alignment_decode E)
            (DyadicShrinkScheduleTasteGate_single_carrier_alignment_decode H)
            (DyadicShrinkScheduleTasteGate_single_carrier_alignment_decode C)
            (DyadicShrinkScheduleTasteGate_single_carrier_alignment_decode P)
            (DyadicShrinkScheduleTasteGate_single_carrier_alignment_decode N))

private theorem dyadicShrinkScheduleToEventFlow_injective
    {x y : DyadicShrinkScheduleUp} :
    dyadicShrinkScheduleToEventFlow x = dyadicShrinkScheduleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicShrinkScheduleFromEventFlow (dyadicShrinkScheduleToEventFlow x) =
        dyadicShrinkScheduleFromEventFlow (dyadicShrinkScheduleToEventFlow y) :=
    congrArg dyadicShrinkScheduleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DyadicShrinkScheduleTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DyadicShrinkScheduleTasteGate_single_carrier_alignment_round_trip y)))

private theorem dyadicShrinkSchedule_field_faithful :
    ∀ x y : DyadicShrinkScheduleUp,
      dyadicShrinkScheduleFields x = dyadicShrinkScheduleFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk k₁ k₁' D₁ W₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk k₂ k₂' D₂ W₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance dyadicShrinkScheduleBHistCarrier : BHistCarrier DyadicShrinkScheduleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicShrinkScheduleToEventFlow
  fromEventFlow := dyadicShrinkScheduleFromEventFlow

instance dyadicShrinkScheduleChapterTasteGate :
    ChapterTasteGate DyadicShrinkScheduleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicShrinkScheduleFromEventFlow (dyadicShrinkScheduleToEventFlow x) = some x
    exact DyadicShrinkScheduleTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicShrinkScheduleToEventFlow_injective heq)

instance dyadicShrinkScheduleFieldFaithful : FieldFaithful DyadicShrinkScheduleUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicShrinkScheduleFields
  field_faithful := dyadicShrinkSchedule_field_faithful

instance dyadicShrinkScheduleNontrivial :
    BEDC.Meta.TasteGate.Nontrivial DyadicShrinkScheduleUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicShrinkScheduleUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DyadicShrinkScheduleUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DyadicShrinkScheduleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicShrinkScheduleChapterTasteGate

theorem DyadicShrinkScheduleTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DyadicShrinkScheduleUp) ∧
      Nonempty (FieldFaithful DyadicShrinkScheduleUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial DyadicShrinkScheduleUp) ∧
      (∀ h : BHist,
        dyadicShrinkScheduleDecodeBHist (dyadicShrinkScheduleEncodeBHist h) = h) ∧
      (∀ x : DyadicShrinkScheduleUp,
        dyadicShrinkScheduleFromEventFlow (dyadicShrinkScheduleToEventFlow x) = some x) ∧
      (∀ x y : DyadicShrinkScheduleUp,
        dyadicShrinkScheduleToEventFlow x = dyadicShrinkScheduleToEventFlow y → x = y) ∧
      dyadicShrinkScheduleEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨dyadicShrinkScheduleChapterTasteGate⟩
  constructor
  · exact ⟨dyadicShrinkScheduleFieldFaithful⟩
  constructor
  · exact ⟨dyadicShrinkScheduleNontrivial⟩
  constructor
  · exact DyadicShrinkScheduleTasteGate_single_carrier_alignment_decode
  constructor
  · exact DyadicShrinkScheduleTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact dyadicShrinkScheduleToEventFlow_injective heq
  · rfl

end BEDC.Derived.DyadicShrinkScheduleUp
