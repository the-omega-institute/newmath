import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformCauchyEmbeddingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformCauchyEmbeddingUp : Type where
  | mk (C S R T E V H K P N : BHist) : UniformCauchyEmbeddingUp
  deriving DecidableEq

def uniformCauchyEmbeddingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformCauchyEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformCauchyEmbeddingEncodeBHist h

def uniformCauchyEmbeddingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformCauchyEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformCauchyEmbeddingDecodeBHist tail)

private theorem uniformCauchyEmbeddingDecode_encode_bhist :
    ∀ h : BHist,
      uniformCauchyEmbeddingDecodeBHist (uniformCauchyEmbeddingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformCauchyEmbeddingFields : UniformCauchyEmbeddingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformCauchyEmbeddingUp.mk C S R T E V H K P N => [C, S, R, T, E, V, H, K, P, N]

def uniformCauchyEmbeddingToEventFlow : UniformCauchyEmbeddingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformCauchyEmbeddingFields x).map uniformCauchyEmbeddingEncodeBHist

def uniformCauchyEmbeddingFromEventFlow :
    EventFlow → Option UniformCauchyEmbeddingUp
  -- BEDC touchpoint anchor: BHist BMark
  | C :: S :: R :: T :: E :: V :: H :: K :: P :: N :: [] =>
      some
        (UniformCauchyEmbeddingUp.mk
          (uniformCauchyEmbeddingDecodeBHist C)
          (uniformCauchyEmbeddingDecodeBHist S)
          (uniformCauchyEmbeddingDecodeBHist R)
          (uniformCauchyEmbeddingDecodeBHist T)
          (uniformCauchyEmbeddingDecodeBHist E)
          (uniformCauchyEmbeddingDecodeBHist V)
          (uniformCauchyEmbeddingDecodeBHist H)
          (uniformCauchyEmbeddingDecodeBHist K)
          (uniformCauchyEmbeddingDecodeBHist P)
          (uniformCauchyEmbeddingDecodeBHist N))
  | _ => none

private theorem uniformCauchyEmbedding_round_trip :
    ∀ x : UniformCauchyEmbeddingUp,
      uniformCauchyEmbeddingFromEventFlow (uniformCauchyEmbeddingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk C S R T E V H K P N =>
      change
        some
            (UniformCauchyEmbeddingUp.mk
              (uniformCauchyEmbeddingDecodeBHist (uniformCauchyEmbeddingEncodeBHist C))
              (uniformCauchyEmbeddingDecodeBHist (uniformCauchyEmbeddingEncodeBHist S))
              (uniformCauchyEmbeddingDecodeBHist (uniformCauchyEmbeddingEncodeBHist R))
              (uniformCauchyEmbeddingDecodeBHist (uniformCauchyEmbeddingEncodeBHist T))
              (uniformCauchyEmbeddingDecodeBHist (uniformCauchyEmbeddingEncodeBHist E))
              (uniformCauchyEmbeddingDecodeBHist (uniformCauchyEmbeddingEncodeBHist V))
              (uniformCauchyEmbeddingDecodeBHist (uniformCauchyEmbeddingEncodeBHist H))
              (uniformCauchyEmbeddingDecodeBHist (uniformCauchyEmbeddingEncodeBHist K))
              (uniformCauchyEmbeddingDecodeBHist (uniformCauchyEmbeddingEncodeBHist P))
              (uniformCauchyEmbeddingDecodeBHist (uniformCauchyEmbeddingEncodeBHist N))) =
          some (UniformCauchyEmbeddingUp.mk C S R T E V H K P N)
      rw [uniformCauchyEmbeddingDecode_encode_bhist C,
        uniformCauchyEmbeddingDecode_encode_bhist S,
        uniformCauchyEmbeddingDecode_encode_bhist R,
        uniformCauchyEmbeddingDecode_encode_bhist T,
        uniformCauchyEmbeddingDecode_encode_bhist E,
        uniformCauchyEmbeddingDecode_encode_bhist V,
        uniformCauchyEmbeddingDecode_encode_bhist H,
        uniformCauchyEmbeddingDecode_encode_bhist K,
        uniformCauchyEmbeddingDecode_encode_bhist P,
        uniformCauchyEmbeddingDecode_encode_bhist N]

private theorem uniformCauchyEmbeddingToEventFlow_injective
    {x y : UniformCauchyEmbeddingUp} :
    uniformCauchyEmbeddingToEventFlow x = uniformCauchyEmbeddingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformCauchyEmbeddingFromEventFlow (uniformCauchyEmbeddingToEventFlow x) =
        uniformCauchyEmbeddingFromEventFlow (uniformCauchyEmbeddingToEventFlow y) :=
    congrArg uniformCauchyEmbeddingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformCauchyEmbedding_round_trip x).symm
      (Eq.trans hread (uniformCauchyEmbedding_round_trip y)))

private theorem uniformCauchyEmbedding_fields_faithful :
    ∀ x y : UniformCauchyEmbeddingUp,
      uniformCauchyEmbeddingFields x = uniformCauchyEmbeddingFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk C S R T E V H K P N =>
      cases y with
      | mk C' S' R' T' E' V' H' K' P' N' =>
          cases hfields
          rfl

instance uniformCauchyEmbeddingBHistCarrier : BHistCarrier UniformCauchyEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformCauchyEmbeddingToEventFlow
  fromEventFlow := uniformCauchyEmbeddingFromEventFlow

instance uniformCauchyEmbeddingChapterTasteGate :
    ChapterTasteGate UniformCauchyEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformCauchyEmbeddingFromEventFlow (uniformCauchyEmbeddingToEventFlow x) = some x
    exact uniformCauchyEmbedding_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformCauchyEmbeddingToEventFlow_injective heq)

instance uniformCauchyEmbeddingFieldFaithful :
    FieldFaithful UniformCauchyEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformCauchyEmbeddingFields
  field_faithful := uniformCauchyEmbedding_fields_faithful

instance uniformCauchyEmbeddingNontrivial : Nontrivial UniformCauchyEmbeddingUp where
  witness_pair :=
    ⟨UniformCauchyEmbeddingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniformCauchyEmbeddingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def uniformCauchyEmbeddingTasteGate : ChapterTasteGate UniformCauchyEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformCauchyEmbeddingChapterTasteGate

end BEDC.Derived.UniformCauchyEmbeddingUp
