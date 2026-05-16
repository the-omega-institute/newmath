import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PredictiveDescentUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PredictiveDescentUp : Type where
  | mk (F O K A S X H C P N : BHist) : PredictiveDescentUp
  deriving DecidableEq

def predictiveDescentEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: predictiveDescentEncodeBHist h
  | BHist.e1 h => BMark.b1 :: predictiveDescentEncodeBHist h

def predictiveDescentDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (predictiveDescentDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (predictiveDescentDecodeBHist tail)

private theorem predictiveDescentDecode_encode_bhist :
    ∀ h : BHist, predictiveDescentDecodeBHist (predictiveDescentEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def predictiveDescentToEventFlow : PredictiveDescentUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PredictiveDescentUp.mk F O K A S X H C P N =>
      [[BMark.b0],
        predictiveDescentEncodeBHist F,
        [BMark.b1, BMark.b0],
        predictiveDescentEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b0],
        predictiveDescentEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        predictiveDescentEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        predictiveDescentEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        predictiveDescentEncodeBHist X,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        predictiveDescentEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        predictiveDescentEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        predictiveDescentEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        predictiveDescentEncodeBHist N]

def predictiveDescentFromEventFlow : EventFlow → Option PredictiveDescentUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tagF :: restF =>
      match restF with
      | [] => none
      | F :: restO0 =>
          match restO0 with
          | [] => none
          | _tagO :: restO =>
              match restO with
              | [] => none
              | O :: restK0 =>
                  match restK0 with
                  | [] => none
                  | _tagK :: restK =>
                      match restK with
                      | [] => none
                      | K :: restA0 =>
                          match restA0 with
                          | [] => none
                          | _tagA :: restA =>
                              match restA with
                              | [] => none
                              | A :: restS0 =>
                                  match restS0 with
                                  | [] => none
                                  | _tagS :: restS =>
                                      match restS with
                                      | [] => none
                                      | S :: restX0 =>
                                          match restX0 with
                                          | [] => none
                                          | _tagX :: restX =>
                                              match restX with
                                              | [] => none
                                              | X :: restH0 =>
                                                  match restH0 with
                                                  | [] => none
                                                  | _tagH :: restH =>
                                                      match restH with
                                                      | [] => none
                                                      | H :: restC0 =>
                                                          match restC0 with
                                                          | [] => none
                                                          | _tagC :: restC =>
                                                              match restC with
                                                              | [] => none
                                                              | C :: restP0 =>
                                                                  match restP0 with
                                                                  | [] => none
                                                                  | _tagP :: restP =>
                                                                      match restP with
                                                                      | [] => none
                                                                      | P :: restN0 =>
                                                                          match restN0 with
                                                                          | [] => none
                                                                          | _tagN :: restN =>
                                                                              match restN with
                                                                              | [] => none
                                                                              | N :: restDone =>
                                                                                  match restDone with
                                                                                  | [] =>
                                                                                      some
                                                                                        (PredictiveDescentUp.mk
                                                                                          (predictiveDescentDecodeBHist F)
                                                                                          (predictiveDescentDecodeBHist O)
                                                                                          (predictiveDescentDecodeBHist K)
                                                                                          (predictiveDescentDecodeBHist A)
                                                                                          (predictiveDescentDecodeBHist S)
                                                                                          (predictiveDescentDecodeBHist X)
                                                                                          (predictiveDescentDecodeBHist H)
                                                                                          (predictiveDescentDecodeBHist C)
                                                                                          (predictiveDescentDecodeBHist P)
                                                                                          (predictiveDescentDecodeBHist N))
                                                                                  | _ :: _ => none

private theorem predictiveDescent_round_trip :
    ∀ x : PredictiveDescentUp,
      predictiveDescentFromEventFlow (predictiveDescentToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F O K A S X H C P N =>
      change
        some
            (PredictiveDescentUp.mk
              (predictiveDescentDecodeBHist (predictiveDescentEncodeBHist F))
              (predictiveDescentDecodeBHist (predictiveDescentEncodeBHist O))
              (predictiveDescentDecodeBHist (predictiveDescentEncodeBHist K))
              (predictiveDescentDecodeBHist (predictiveDescentEncodeBHist A))
              (predictiveDescentDecodeBHist (predictiveDescentEncodeBHist S))
              (predictiveDescentDecodeBHist (predictiveDescentEncodeBHist X))
              (predictiveDescentDecodeBHist (predictiveDescentEncodeBHist H))
              (predictiveDescentDecodeBHist (predictiveDescentEncodeBHist C))
              (predictiveDescentDecodeBHist (predictiveDescentEncodeBHist P))
              (predictiveDescentDecodeBHist (predictiveDescentEncodeBHist N))) =
          some (PredictiveDescentUp.mk F O K A S X H C P N)
      rw [predictiveDescentDecode_encode_bhist F,
        predictiveDescentDecode_encode_bhist O,
        predictiveDescentDecode_encode_bhist K,
        predictiveDescentDecode_encode_bhist A,
        predictiveDescentDecode_encode_bhist S,
        predictiveDescentDecode_encode_bhist X,
        predictiveDescentDecode_encode_bhist H,
        predictiveDescentDecode_encode_bhist C,
        predictiveDescentDecode_encode_bhist P,
        predictiveDescentDecode_encode_bhist N]

private theorem predictiveDescentToEventFlow_injective {x y : PredictiveDescentUp} :
    predictiveDescentToEventFlow x = predictiveDescentToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      predictiveDescentFromEventFlow (predictiveDescentToEventFlow x) =
        predictiveDescentFromEventFlow (predictiveDescentToEventFlow y) :=
    congrArg predictiveDescentFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (predictiveDescent_round_trip x).symm
      (Eq.trans hread (predictiveDescent_round_trip y)))

instance predictiveDescentBHistCarrier : BHistCarrier PredictiveDescentUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := predictiveDescentToEventFlow
  fromEventFlow := predictiveDescentFromEventFlow

instance predictiveDescentChapterTasteGate : ChapterTasteGate PredictiveDescentUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change predictiveDescentFromEventFlow (predictiveDescentToEventFlow x) = some x
    exact predictiveDescent_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (predictiveDescentToEventFlow_injective heq)

instance predictiveDescentFieldFaithful : FieldFaithful PredictiveDescentUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | PredictiveDescentUp.mk F O K A S X H C P N => [F, O, K, A, S, X, H, C, P, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk F₁ O₁ K₁ A₁ S₁ X₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk F₂ O₂ K₂ A₂ S₂ X₂ H₂ C₂ P₂ N₂ =>
            simp only [] at h
            cases h
            rfl

instance predictiveDescentNontrivial : Nontrivial PredictiveDescentUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PredictiveDescentUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PredictiveDescentUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PredictiveDescentUp :=
  -- BEDC touchpoint anchor: BHist BMark
  predictiveDescentChapterTasteGate

theorem PredictiveDescentTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier PredictiveDescentUp) ∧
      Nonempty (ChapterTasteGate PredictiveDescentUp) ∧
        Nonempty (FieldFaithful PredictiveDescentUp) ∧
          Nonempty (Nontrivial PredictiveDescentUp) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨⟨predictiveDescentBHistCarrier⟩,
      ⟨predictiveDescentChapterTasteGate⟩,
      ⟨predictiveDescentFieldFaithful⟩,
      ⟨predictiveDescentNontrivial⟩⟩

end BEDC.Derived.PredictiveDescentUp
