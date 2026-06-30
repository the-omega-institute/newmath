import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformIntegrabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformIntegrabilityUp : Type where
  | mk (M I F T B H C P N : BHist) : UniformIntegrabilityUp
  deriving DecidableEq

def uniformIntegrabilityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformIntegrabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformIntegrabilityEncodeBHist h

def uniformIntegrabilityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformIntegrabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformIntegrabilityDecodeBHist tail)

private theorem UniformIntegrabilityTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      uniformIntegrabilityDecodeBHist (uniformIntegrabilityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformIntegrabilityToEventFlow : UniformIntegrabilityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | UniformIntegrabilityUp.mk M I F T B H C P N =>
      [[BMark.b0],
        uniformIntegrabilityEncodeBHist M,
        [BMark.b1, BMark.b0],
        uniformIntegrabilityEncodeBHist I,
        [BMark.b1, BMark.b1, BMark.b0],
        uniformIntegrabilityEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        uniformIntegrabilityEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        uniformIntegrabilityEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        uniformIntegrabilityEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        uniformIntegrabilityEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        uniformIntegrabilityEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        uniformIntegrabilityEncodeBHist N]

def uniformIntegrabilityFromEventFlow : EventFlow → Option UniformIntegrabilityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tagM :: restM =>
      match restM with
      | [] => none
      | M :: restITag =>
          match restITag with
          | [] => none
          | _tagI :: restI =>
              match restI with
              | [] => none
              | I :: restFTag =>
                  match restFTag with
                  | [] => none
                  | _tagF :: restF =>
                      match restF with
                      | [] => none
                      | F :: restTTag =>
                          match restTTag with
                          | [] => none
                          | _tagT :: restT =>
                              match restT with
                              | [] => none
                              | T :: restBTag =>
                                  match restBTag with
                                  | [] => none
                                  | _tagB :: restB =>
                                      match restB with
                                      | [] => none
                                      | B :: restHTag =>
                                          match restHTag with
                                          | [] => none
                                          | _tagH :: restH =>
                                              match restH with
                                              | [] => none
                                              | H :: restCTag =>
                                                  match restCTag with
                                                  | [] => none
                                                  | _tagC :: restC =>
                                                      match restC with
                                                      | [] => none
                                                      | C :: restPTag =>
                                                          match restPTag with
                                                          | [] => none
                                                          | _tagP :: restP =>
                                                              match restP with
                                                              | [] => none
                                                              | P :: restNTag =>
                                                                  match restNTag with
                                                                  | [] => none
                                                                  | _tagN :: restN =>
                                                                      match restN with
                                                                      | [] => none
                                                                      | N :: rest =>
                                                                          match rest with
                                                                          | [] =>
                                                                              some
                                                                                (UniformIntegrabilityUp.mk
                                                                                  (uniformIntegrabilityDecodeBHist M)
                                                                                  (uniformIntegrabilityDecodeBHist I)
                                                                                  (uniformIntegrabilityDecodeBHist F)
                                                                                  (uniformIntegrabilityDecodeBHist T)
                                                                                  (uniformIntegrabilityDecodeBHist B)
                                                                                  (uniformIntegrabilityDecodeBHist H)
                                                                                  (uniformIntegrabilityDecodeBHist C)
                                                                                  (uniformIntegrabilityDecodeBHist P)
                                                                                  (uniformIntegrabilityDecodeBHist N))
                                                                          | _ :: _ => none

private theorem UniformIntegrabilityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UniformIntegrabilityUp,
      uniformIntegrabilityFromEventFlow (uniformIntegrabilityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M I F T B H C P N =>
      change
        some
          (UniformIntegrabilityUp.mk
            (uniformIntegrabilityDecodeBHist (uniformIntegrabilityEncodeBHist M))
            (uniformIntegrabilityDecodeBHist (uniformIntegrabilityEncodeBHist I))
            (uniformIntegrabilityDecodeBHist (uniformIntegrabilityEncodeBHist F))
            (uniformIntegrabilityDecodeBHist (uniformIntegrabilityEncodeBHist T))
            (uniformIntegrabilityDecodeBHist (uniformIntegrabilityEncodeBHist B))
            (uniformIntegrabilityDecodeBHist (uniformIntegrabilityEncodeBHist H))
            (uniformIntegrabilityDecodeBHist (uniformIntegrabilityEncodeBHist C))
            (uniformIntegrabilityDecodeBHist (uniformIntegrabilityEncodeBHist P))
            (uniformIntegrabilityDecodeBHist (uniformIntegrabilityEncodeBHist N))) =
          some (UniformIntegrabilityUp.mk M I F T B H C P N)
      rw [UniformIntegrabilityTasteGate_single_carrier_alignment_decode M,
        UniformIntegrabilityTasteGate_single_carrier_alignment_decode I,
        UniformIntegrabilityTasteGate_single_carrier_alignment_decode F,
        UniformIntegrabilityTasteGate_single_carrier_alignment_decode T,
        UniformIntegrabilityTasteGate_single_carrier_alignment_decode B,
        UniformIntegrabilityTasteGate_single_carrier_alignment_decode H,
        UniformIntegrabilityTasteGate_single_carrier_alignment_decode C,
        UniformIntegrabilityTasteGate_single_carrier_alignment_decode P,
        UniformIntegrabilityTasteGate_single_carrier_alignment_decode N]

private theorem UniformIntegrabilityTasteGate_single_carrier_alignment_injective
    {x y : UniformIntegrabilityUp} :
    uniformIntegrabilityToEventFlow x = uniformIntegrabilityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformIntegrabilityFromEventFlow (uniformIntegrabilityToEventFlow x) =
        uniformIntegrabilityFromEventFlow (uniformIntegrabilityToEventFlow y) :=
    congrArg uniformIntegrabilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (UniformIntegrabilityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (UniformIntegrabilityTasteGate_single_carrier_alignment_round_trip y)))

instance uniformIntegrabilityBHistCarrier : BHistCarrier UniformIntegrabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformIntegrabilityToEventFlow
  fromEventFlow := uniformIntegrabilityFromEventFlow

instance uniformIntegrabilityChapterTasteGate :
    ChapterTasteGate UniformIntegrabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformIntegrabilityFromEventFlow (uniformIntegrabilityToEventFlow x) = some x
    exact UniformIntegrabilityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UniformIntegrabilityTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate UniformIntegrabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformIntegrabilityChapterTasteGate

theorem UniformIntegrabilityTasteGate_single_carrier_alignment :
    (∀ h : BHist, uniformIntegrabilityDecodeBHist (uniformIntegrabilityEncodeBHist h) = h) ∧
      (∀ x : UniformIntegrabilityUp,
        uniformIntegrabilityFromEventFlow (uniformIntegrabilityToEventFlow x) = some x) ∧
        (∀ x y : UniformIntegrabilityUp,
          uniformIntegrabilityToEventFlow x = uniformIntegrabilityToEventFlow y → x = y) ∧
          uniformIntegrabilityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact UniformIntegrabilityTasteGate_single_carrier_alignment_decode
  constructor
  · exact UniformIntegrabilityTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact UniformIntegrabilityTasteGate_single_carrier_alignment_injective heq
  · rfl

end BEDC.Derived.UniformIntegrabilityUp
