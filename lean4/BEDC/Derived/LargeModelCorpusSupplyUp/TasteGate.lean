import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LargeModelCorpusSupplyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LargeModelCorpusSupplyUp : Type where
  | mk : (R F W I A H K P N : BHist) → LargeModelCorpusSupplyUp
  deriving DecidableEq

def largeModelCorpusSupplyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: largeModelCorpusSupplyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: largeModelCorpusSupplyEncodeBHist h

def largeModelCorpusSupplyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (largeModelCorpusSupplyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (largeModelCorpusSupplyDecodeBHist tail)

private theorem largeModelCorpusSupplyDecodeEncodeBHist :
    ∀ h : BHist,
      largeModelCorpusSupplyDecodeBHist (largeModelCorpusSupplyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def largeModelCorpusSupplyFields : LargeModelCorpusSupplyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LargeModelCorpusSupplyUp.mk R F W I A H K P N => [R, F, W, I, A, H, K, P, N]

def largeModelCorpusSupplyToEventFlow : LargeModelCorpusSupplyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (largeModelCorpusSupplyFields x).map largeModelCorpusSupplyEncodeBHist

def largeModelCorpusSupplyFromEventFlow : EventFlow → Option LargeModelCorpusSupplyUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | R :: rest0 =>
      match rest0 with
      | [] => none
      | F :: rest1 =>
          match rest1 with
          | [] => none
          | W :: rest2 =>
              match rest2 with
              | [] => none
              | I :: rest3 =>
                  match rest3 with
                  | [] => none
                  | A :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | K :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (LargeModelCorpusSupplyUp.mk
                                              (largeModelCorpusSupplyDecodeBHist R)
                                              (largeModelCorpusSupplyDecodeBHist F)
                                              (largeModelCorpusSupplyDecodeBHist W)
                                              (largeModelCorpusSupplyDecodeBHist I)
                                              (largeModelCorpusSupplyDecodeBHist A)
                                              (largeModelCorpusSupplyDecodeBHist H)
                                              (largeModelCorpusSupplyDecodeBHist K)
                                              (largeModelCorpusSupplyDecodeBHist P)
                                              (largeModelCorpusSupplyDecodeBHist N))
                                      | _ :: _ => none

private theorem largeModelCorpusSupply_round_trip :
    ∀ x : LargeModelCorpusSupplyUp,
      largeModelCorpusSupplyFromEventFlow
        (largeModelCorpusSupplyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R F W I A H K P N =>
      change
        some
          (LargeModelCorpusSupplyUp.mk
            (largeModelCorpusSupplyDecodeBHist (largeModelCorpusSupplyEncodeBHist R))
            (largeModelCorpusSupplyDecodeBHist (largeModelCorpusSupplyEncodeBHist F))
            (largeModelCorpusSupplyDecodeBHist (largeModelCorpusSupplyEncodeBHist W))
            (largeModelCorpusSupplyDecodeBHist (largeModelCorpusSupplyEncodeBHist I))
            (largeModelCorpusSupplyDecodeBHist (largeModelCorpusSupplyEncodeBHist A))
            (largeModelCorpusSupplyDecodeBHist (largeModelCorpusSupplyEncodeBHist H))
            (largeModelCorpusSupplyDecodeBHist (largeModelCorpusSupplyEncodeBHist K))
            (largeModelCorpusSupplyDecodeBHist (largeModelCorpusSupplyEncodeBHist P))
            (largeModelCorpusSupplyDecodeBHist (largeModelCorpusSupplyEncodeBHist N))) =
          some (LargeModelCorpusSupplyUp.mk R F W I A H K P N)
      rw [largeModelCorpusSupplyDecodeEncodeBHist R,
        largeModelCorpusSupplyDecodeEncodeBHist F, largeModelCorpusSupplyDecodeEncodeBHist W,
        largeModelCorpusSupplyDecodeEncodeBHist I, largeModelCorpusSupplyDecodeEncodeBHist A,
        largeModelCorpusSupplyDecodeEncodeBHist H, largeModelCorpusSupplyDecodeEncodeBHist K,
        largeModelCorpusSupplyDecodeEncodeBHist P, largeModelCorpusSupplyDecodeEncodeBHist N]

private theorem largeModelCorpusSupplyToEventFlow_injective
    {x y : LargeModelCorpusSupplyUp} :
    largeModelCorpusSupplyToEventFlow x = largeModelCorpusSupplyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      largeModelCorpusSupplyFromEventFlow (largeModelCorpusSupplyToEventFlow x) =
        largeModelCorpusSupplyFromEventFlow (largeModelCorpusSupplyToEventFlow y) :=
    congrArg largeModelCorpusSupplyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (largeModelCorpusSupply_round_trip x).symm
      (Eq.trans hread (largeModelCorpusSupply_round_trip y)))

private theorem largeModelCorpusSupply_fields_faithful :
    ∀ x y : LargeModelCorpusSupplyUp,
      largeModelCorpusSupplyFields x = largeModelCorpusSupplyFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R₁ F₁ W₁ I₁ A₁ H₁ K₁ P₁ N₁ =>
      cases y with
      | mk R₂ F₂ W₂ I₂ A₂ H₂ K₂ P₂ N₂ =>
          injection hfields with hR tail0
          injection tail0 with hF tail1
          injection tail1 with hW tail2
          injection tail2 with hI tail3
          injection tail3 with hA tail4
          injection tail4 with hH tail5
          injection tail5 with hK tail6
          injection tail6 with hP tail7
          injection tail7 with hN _
          subst hR
          subst hF
          subst hW
          subst hI
          subst hA
          subst hH
          subst hK
          subst hP
          subst hN
          rfl

instance largeModelCorpusSupplyBHistCarrier : BHistCarrier LargeModelCorpusSupplyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := largeModelCorpusSupplyToEventFlow
  fromEventFlow := largeModelCorpusSupplyFromEventFlow

instance largeModelCorpusSupplyChapterTasteGate :
    ChapterTasteGate LargeModelCorpusSupplyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change largeModelCorpusSupplyFromEventFlow
      (largeModelCorpusSupplyToEventFlow x) = some x
    exact largeModelCorpusSupply_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (largeModelCorpusSupplyToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LargeModelCorpusSupplyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change largeModelCorpusSupplyFromEventFlow
      (largeModelCorpusSupplyToEventFlow x) = some x
    exact largeModelCorpusSupply_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (largeModelCorpusSupplyToEventFlow_injective heq)

instance largeModelCorpusSupplyFieldFaithful : FieldFaithful LargeModelCorpusSupplyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := largeModelCorpusSupplyFields
  field_faithful := largeModelCorpusSupply_fields_faithful

instance largeModelCorpusSupplyNontrivial : Nontrivial LargeModelCorpusSupplyUp where
  witness_pair :=
    ⟨LargeModelCorpusSupplyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LargeModelCorpusSupplyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

theorem LargeModelCorpusSupplyTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      largeModelCorpusSupplyDecodeBHist (largeModelCorpusSupplyEncodeBHist h) = h) ∧
      (∀ x : LargeModelCorpusSupplyUp,
        largeModelCorpusSupplyFromEventFlow (largeModelCorpusSupplyToEventFlow x) = some x) ∧
        (∀ x y : LargeModelCorpusSupplyUp,
          largeModelCorpusSupplyToEventFlow x =
            largeModelCorpusSupplyToEventFlow y → x = y) ∧
          largeModelCorpusSupplyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact largeModelCorpusSupplyDecodeEncodeBHist
  · constructor
    · exact largeModelCorpusSupply_round_trip
    · constructor
      · intro x y heq
        exact largeModelCorpusSupplyToEventFlow_injective heq
      · rfl

end BEDC.Derived.LargeModelCorpusSupplyUp
