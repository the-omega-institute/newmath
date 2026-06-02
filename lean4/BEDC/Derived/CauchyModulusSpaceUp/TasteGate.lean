import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyModulusSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyModulusSpaceUp : Type where
  | mk (I S W D R Q H C P N : BHist) : CauchyModulusSpaceUp
  deriving DecidableEq

def cauchyModulusSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyModulusSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyModulusSpaceEncodeBHist h

def cauchyModulusSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyModulusSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyModulusSpaceDecodeBHist tail)

private theorem cauchyModulusSpaceDecode_encode_bhist :
    ∀ h : BHist, cauchyModulusSpaceDecodeBHist (cauchyModulusSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyModulusSpaceFields : CauchyModulusSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyModulusSpaceUp.mk I S W D R Q H C P N => [I, S, W, D, R, Q, H, C, P, N]

def cauchyModulusSpaceToEventFlow : CauchyModulusSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyModulusSpaceFields x).map cauchyModulusSpaceEncodeBHist

def cauchyModulusSpaceFromEventFlow : EventFlow → Option CauchyModulusSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | I :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | W :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | Q :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (CauchyModulusSpaceUp.mk
                                                  (cauchyModulusSpaceDecodeBHist I)
                                                  (cauchyModulusSpaceDecodeBHist S)
                                                  (cauchyModulusSpaceDecodeBHist W)
                                                  (cauchyModulusSpaceDecodeBHist D)
                                                  (cauchyModulusSpaceDecodeBHist R)
                                                  (cauchyModulusSpaceDecodeBHist Q)
                                                  (cauchyModulusSpaceDecodeBHist H)
                                                  (cauchyModulusSpaceDecodeBHist C)
                                                  (cauchyModulusSpaceDecodeBHist P)
                                                  (cauchyModulusSpaceDecodeBHist N))
                                          | _ :: _ => none

private theorem cauchyModulusSpace_round_trip (x : CauchyModulusSpaceUp) :
    cauchyModulusSpaceFromEventFlow (cauchyModulusSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I S W D R Q H C P N =>
      change
        some
          (CauchyModulusSpaceUp.mk
            (cauchyModulusSpaceDecodeBHist (cauchyModulusSpaceEncodeBHist I))
            (cauchyModulusSpaceDecodeBHist (cauchyModulusSpaceEncodeBHist S))
            (cauchyModulusSpaceDecodeBHist (cauchyModulusSpaceEncodeBHist W))
            (cauchyModulusSpaceDecodeBHist (cauchyModulusSpaceEncodeBHist D))
            (cauchyModulusSpaceDecodeBHist (cauchyModulusSpaceEncodeBHist R))
            (cauchyModulusSpaceDecodeBHist (cauchyModulusSpaceEncodeBHist Q))
            (cauchyModulusSpaceDecodeBHist (cauchyModulusSpaceEncodeBHist H))
            (cauchyModulusSpaceDecodeBHist (cauchyModulusSpaceEncodeBHist C))
            (cauchyModulusSpaceDecodeBHist (cauchyModulusSpaceEncodeBHist P))
            (cauchyModulusSpaceDecodeBHist (cauchyModulusSpaceEncodeBHist N))) =
          some (CauchyModulusSpaceUp.mk I S W D R Q H C P N)
      rw [cauchyModulusSpaceDecode_encode_bhist I, cauchyModulusSpaceDecode_encode_bhist S,
        cauchyModulusSpaceDecode_encode_bhist W, cauchyModulusSpaceDecode_encode_bhist D,
        cauchyModulusSpaceDecode_encode_bhist R, cauchyModulusSpaceDecode_encode_bhist Q,
        cauchyModulusSpaceDecode_encode_bhist H, cauchyModulusSpaceDecode_encode_bhist C,
        cauchyModulusSpaceDecode_encode_bhist P, cauchyModulusSpaceDecode_encode_bhist N]

private theorem cauchyModulusSpaceToEventFlow_injective {x y : CauchyModulusSpaceUp} :
    cauchyModulusSpaceToEventFlow x = cauchyModulusSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyModulusSpaceFromEventFlow (cauchyModulusSpaceToEventFlow x) =
        cauchyModulusSpaceFromEventFlow (cauchyModulusSpaceToEventFlow y) :=
    congrArg cauchyModulusSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyModulusSpace_round_trip x).symm
      (Eq.trans hread (cauchyModulusSpace_round_trip y)))

private theorem cauchyModulusSpace_field_faithful :
    ∀ x y : CauchyModulusSpaceUp, cauchyModulusSpaceFields x = cauchyModulusSpaceFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ S₁ W₁ D₁ R₁ Q₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk I₂ S₂ W₂ D₂ R₂ Q₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cauchyModulusSpaceBHistCarrier : BHistCarrier CauchyModulusSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyModulusSpaceToEventFlow
  fromEventFlow := cauchyModulusSpaceFromEventFlow

instance cauchyModulusSpaceChapterTasteGate :
    ChapterTasteGate CauchyModulusSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyModulusSpaceFromEventFlow (cauchyModulusSpaceToEventFlow x) = some x
    exact cauchyModulusSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyModulusSpaceToEventFlow_injective heq)

instance cauchyModulusSpaceFieldFaithful :
    FieldFaithful CauchyModulusSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyModulusSpaceFields
  field_faithful := cauchyModulusSpace_field_faithful

instance cauchyModulusSpaceNontrivial : Nontrivial CauchyModulusSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyModulusSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyModulusSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CauchyModulusSpaceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyModulusSpaceUp) ∧
      Nonempty (FieldFaithful CauchyModulusSpaceUp) ∧
        Nonempty (Nontrivial CauchyModulusSpaceUp) ∧
          (∀ h : BHist, cauchyModulusSpaceDecodeBHist (cauchyModulusSpaceEncodeBHist h) = h) ∧
            (∀ x : CauchyModulusSpaceUp,
              cauchyModulusSpaceFromEventFlow (cauchyModulusSpaceToEventFlow x) = some x) ∧
              cauchyModulusSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨cauchyModulusSpaceChapterTasteGate⟩, ⟨cauchyModulusSpaceFieldFaithful⟩,
      ⟨cauchyModulusSpaceNontrivial⟩, cauchyModulusSpaceDecode_encode_bhist,
      cauchyModulusSpace_round_trip, rfl⟩

end BEDC.Derived.CauchyModulusSpaceUp
