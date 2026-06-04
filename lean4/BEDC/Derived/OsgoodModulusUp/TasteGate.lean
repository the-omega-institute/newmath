import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OsgoodModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OsgoodModulusUp : Type where
  | mk (O V A T Q R L H C P N : BHist) : OsgoodModulusUp
  deriving DecidableEq

def osgoodModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: osgoodModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: osgoodModulusEncodeBHist h

def osgoodModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (osgoodModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (osgoodModulusDecodeBHist tail)

private theorem OsgoodModulusTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, osgoodModulusDecodeBHist (osgoodModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def osgoodModulusFields : OsgoodModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OsgoodModulusUp.mk O V A T Q R L H C P N => [O, V, A, T, Q, R, L, H, C, P, N]

def osgoodModulusToEventFlow : OsgoodModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (osgoodModulusFields x).map osgoodModulusEncodeBHist

def osgoodModulusFromEventFlow : EventFlow → Option OsgoodModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | O :: V :: A :: T :: Q :: R :: L :: H :: C :: P :: N :: [] =>
      some
        (OsgoodModulusUp.mk
          (osgoodModulusDecodeBHist O)
          (osgoodModulusDecodeBHist V)
          (osgoodModulusDecodeBHist A)
          (osgoodModulusDecodeBHist T)
          (osgoodModulusDecodeBHist Q)
          (osgoodModulusDecodeBHist R)
          (osgoodModulusDecodeBHist L)
          (osgoodModulusDecodeBHist H)
          (osgoodModulusDecodeBHist C)
          (osgoodModulusDecodeBHist P)
          (osgoodModulusDecodeBHist N))
  | _ => none

private theorem OsgoodModulusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : OsgoodModulusUp,
      osgoodModulusFromEventFlow (osgoodModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O V A T Q R L H C P N =>
      change
        some
          (OsgoodModulusUp.mk
            (osgoodModulusDecodeBHist (osgoodModulusEncodeBHist O))
            (osgoodModulusDecodeBHist (osgoodModulusEncodeBHist V))
            (osgoodModulusDecodeBHist (osgoodModulusEncodeBHist A))
            (osgoodModulusDecodeBHist (osgoodModulusEncodeBHist T))
            (osgoodModulusDecodeBHist (osgoodModulusEncodeBHist Q))
            (osgoodModulusDecodeBHist (osgoodModulusEncodeBHist R))
            (osgoodModulusDecodeBHist (osgoodModulusEncodeBHist L))
            (osgoodModulusDecodeBHist (osgoodModulusEncodeBHist H))
            (osgoodModulusDecodeBHist (osgoodModulusEncodeBHist C))
            (osgoodModulusDecodeBHist (osgoodModulusEncodeBHist P))
            (osgoodModulusDecodeBHist (osgoodModulusEncodeBHist N))) =
          some (OsgoodModulusUp.mk O V A T Q R L H C P N)
      rw [OsgoodModulusTasteGate_single_carrier_alignment_decode_encode O,
        OsgoodModulusTasteGate_single_carrier_alignment_decode_encode V,
        OsgoodModulusTasteGate_single_carrier_alignment_decode_encode A,
        OsgoodModulusTasteGate_single_carrier_alignment_decode_encode T,
        OsgoodModulusTasteGate_single_carrier_alignment_decode_encode Q,
        OsgoodModulusTasteGate_single_carrier_alignment_decode_encode R,
        OsgoodModulusTasteGate_single_carrier_alignment_decode_encode L,
        OsgoodModulusTasteGate_single_carrier_alignment_decode_encode H,
        OsgoodModulusTasteGate_single_carrier_alignment_decode_encode C,
        OsgoodModulusTasteGate_single_carrier_alignment_decode_encode P,
        OsgoodModulusTasteGate_single_carrier_alignment_decode_encode N]

private theorem OsgoodModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : OsgoodModulusUp} :
    osgoodModulusToEventFlow x = osgoodModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      osgoodModulusFromEventFlow (osgoodModulusToEventFlow x) =
        osgoodModulusFromEventFlow (osgoodModulusToEventFlow y) :=
    congrArg osgoodModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (OsgoodModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (OsgoodModulusTasteGate_single_carrier_alignment_round_trip y)))

private theorem OsgoodModulusTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : OsgoodModulusUp, osgoodModulusFields x = osgoodModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk O₁ V₁ A₁ T₁ Q₁ R₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk O₂ V₂ A₂ T₂ Q₂ R₂ L₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance osgoodModulusBHistCarrier : BHistCarrier OsgoodModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := osgoodModulusToEventFlow
  fromEventFlow := osgoodModulusFromEventFlow

instance osgoodModulusChapterTasteGate : ChapterTasteGate OsgoodModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change osgoodModulusFromEventFlow (osgoodModulusToEventFlow x) = some x
    exact OsgoodModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (OsgoodModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance osgoodModulusFieldFaithful : FieldFaithful OsgoodModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := osgoodModulusFields
  field_faithful := OsgoodModulusTasteGate_single_carrier_alignment_fields_faithful

instance osgoodModulusNontrivial : BEDC.Meta.TasteGate.Nontrivial OsgoodModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨OsgoodModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      OsgoodModulusUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate OsgoodModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  osgoodModulusChapterTasteGate

theorem OsgoodModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist, osgoodModulusDecodeBHist (osgoodModulusEncodeBHist h) = h) ∧
      (∀ x y : OsgoodModulusUp, osgoodModulusFields x = osgoodModulusFields y → x = y) ∧
      (∃ x : OsgoodModulusUp,
        osgoodModulusFields x =
          [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty]) ∧
      (∃ y : OsgoodModulusUp,
        osgoodModulusToEventFlow y =
          [[BMark.b1], [], [], [], [], [], [], [], [], [], []]) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact OsgoodModulusTasteGate_single_carrier_alignment_decode_encode
  · exact
      ⟨OsgoodModulusTasteGate_single_carrier_alignment_fields_faithful,
        ⟨OsgoodModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty, rfl⟩,
        ⟨OsgoodModulusUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
          rfl⟩⟩

end BEDC.Derived.OsgoodModulusUp
