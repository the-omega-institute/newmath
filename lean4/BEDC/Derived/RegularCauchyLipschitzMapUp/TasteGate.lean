import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyLipschitzMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyLipschitzMapUp : Type where
  | mk :
      (lipschitz inputName inputWindow outputWindow dyadicLedger outputName realSeal
        transport replay provenance name : BHist) →
        RegularCauchyLipschitzMapUp
  deriving DecidableEq

def regularCauchyLipschitzMapEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyLipschitzMapEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyLipschitzMapEncodeBHist h

def regularCauchyLipschitzMapDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyLipschitzMapDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyLipschitzMapDecodeBHist tail)

private theorem regularCauchyLipschitzMap_decode_encode :
    ∀ h : BHist,
      regularCauchyLipschitzMapDecodeBHist (regularCauchyLipschitzMapEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyLipschitzMapFields :
    RegularCauchyLipschitzMapUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyLipschitzMapUp.mk lipschitz inputName inputWindow outputWindow
      dyadicLedger outputName realSeal transport replay provenance name =>
      [lipschitz, inputName, inputWindow, outputWindow, dyadicLedger, outputName, realSeal,
        transport, replay, provenance, name]

def regularCauchyLipschitzMapToEventFlow :
    RegularCauchyLipschitzMapUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyLipschitzMapFields x).map regularCauchyLipschitzMapEncodeBHist

def regularCauchyLipschitzMapFromEventFlow :
    EventFlow → Option RegularCauchyLipschitzMapUp
  -- BEDC touchpoint anchor: BHist BMark
  | lipschitz :: inputName :: inputWindow :: outputWindow :: dyadicLedger :: outputName ::
      realSeal :: transport :: replay :: provenance :: name :: [] =>
      some
        (RegularCauchyLipschitzMapUp.mk
          (regularCauchyLipschitzMapDecodeBHist lipschitz)
          (regularCauchyLipschitzMapDecodeBHist inputName)
          (regularCauchyLipschitzMapDecodeBHist inputWindow)
          (regularCauchyLipschitzMapDecodeBHist outputWindow)
          (regularCauchyLipschitzMapDecodeBHist dyadicLedger)
          (regularCauchyLipschitzMapDecodeBHist outputName)
          (regularCauchyLipschitzMapDecodeBHist realSeal)
          (regularCauchyLipschitzMapDecodeBHist transport)
          (regularCauchyLipschitzMapDecodeBHist replay)
          (regularCauchyLipschitzMapDecodeBHist provenance)
          (regularCauchyLipschitzMapDecodeBHist name))
  | _ => none

private theorem regularCauchyLipschitzMap_round_trip :
    ∀ x : RegularCauchyLipschitzMapUp,
      regularCauchyLipschitzMapFromEventFlow
          (regularCauchyLipschitzMapToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk lipschitz inputName inputWindow outputWindow dyadicLedger outputName realSeal
      transport replay provenance name =>
      change
        some
          (RegularCauchyLipschitzMapUp.mk
            (regularCauchyLipschitzMapDecodeBHist
              (regularCauchyLipschitzMapEncodeBHist lipschitz))
            (regularCauchyLipschitzMapDecodeBHist
              (regularCauchyLipschitzMapEncodeBHist inputName))
            (regularCauchyLipschitzMapDecodeBHist
              (regularCauchyLipschitzMapEncodeBHist inputWindow))
            (regularCauchyLipschitzMapDecodeBHist
              (regularCauchyLipschitzMapEncodeBHist outputWindow))
            (regularCauchyLipschitzMapDecodeBHist
              (regularCauchyLipschitzMapEncodeBHist dyadicLedger))
            (regularCauchyLipschitzMapDecodeBHist
              (regularCauchyLipschitzMapEncodeBHist outputName))
            (regularCauchyLipschitzMapDecodeBHist
              (regularCauchyLipschitzMapEncodeBHist realSeal))
            (regularCauchyLipschitzMapDecodeBHist
              (regularCauchyLipschitzMapEncodeBHist transport))
            (regularCauchyLipschitzMapDecodeBHist
              (regularCauchyLipschitzMapEncodeBHist replay))
            (regularCauchyLipschitzMapDecodeBHist
              (regularCauchyLipschitzMapEncodeBHist provenance))
            (regularCauchyLipschitzMapDecodeBHist
              (regularCauchyLipschitzMapEncodeBHist name))) =
          some
            (RegularCauchyLipschitzMapUp.mk lipschitz inputName inputWindow outputWindow
              dyadicLedger outputName realSeal transport replay provenance name)
      rw [regularCauchyLipschitzMap_decode_encode lipschitz,
        regularCauchyLipschitzMap_decode_encode inputName,
        regularCauchyLipschitzMap_decode_encode inputWindow,
        regularCauchyLipschitzMap_decode_encode outputWindow,
        regularCauchyLipschitzMap_decode_encode dyadicLedger,
        regularCauchyLipschitzMap_decode_encode outputName,
        regularCauchyLipschitzMap_decode_encode realSeal,
        regularCauchyLipschitzMap_decode_encode transport,
        regularCauchyLipschitzMap_decode_encode replay,
        regularCauchyLipschitzMap_decode_encode provenance,
        regularCauchyLipschitzMap_decode_encode name]

private theorem regularCauchyLipschitzMapToEventFlow_injective
    {x y : RegularCauchyLipschitzMapUp} :
    regularCauchyLipschitzMapToEventFlow x = regularCauchyLipschitzMapToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyLipschitzMapFromEventFlow
          (regularCauchyLipschitzMapToEventFlow x) =
        regularCauchyLipschitzMapFromEventFlow
          (regularCauchyLipschitzMapToEventFlow y) :=
    congrArg regularCauchyLipschitzMapFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyLipschitzMap_round_trip x).symm
      (Eq.trans hread (regularCauchyLipschitzMap_round_trip y)))

private theorem regularCauchyLipschitzMap_field_faithful :
    ∀ x y : RegularCauchyLipschitzMapUp,
      regularCauchyLipschitzMapFields x = regularCauchyLipschitzMapFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk lipschitz₁ inputName₁ inputWindow₁ outputWindow₁ dyadicLedger₁ outputName₁
      realSeal₁ transport₁ replay₁ provenance₁ name₁ =>
      cases y with
      | mk lipschitz₂ inputName₂ inputWindow₂ outputWindow₂ dyadicLedger₂ outputName₂
          realSeal₂ transport₂ replay₂ provenance₂ name₂ =>
          cases hfields
          rfl

instance regularCauchyLipschitzMapBHistCarrier :
    BHistCarrier RegularCauchyLipschitzMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyLipschitzMapToEventFlow
  fromEventFlow := regularCauchyLipschitzMapFromEventFlow

instance regularCauchyLipschitzMapChapterTasteGate :
    ChapterTasteGate RegularCauchyLipschitzMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyLipschitzMapFromEventFlow
          (regularCauchyLipschitzMapToEventFlow x) =
        some x
    exact regularCauchyLipschitzMap_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyLipschitzMapToEventFlow_injective heq)

instance regularCauchyLipschitzMapFieldFaithful :
    FieldFaithful RegularCauchyLipschitzMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyLipschitzMapFields
  field_faithful := regularCauchyLipschitzMap_field_faithful

def taste_gate : ChapterTasteGate RegularCauchyLipschitzMapUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyLipschitzMapChapterTasteGate

theorem RegularCauchyLipschitzMapTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyLipschitzMapDecodeBHist (regularCauchyLipschitzMapEncodeBHist h) =
        h) ∧
      regularCauchyLipschitzMapFields
          (RegularCauchyLipschitzMapUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyLipschitzMap_decode_encode
  · rfl

end BEDC.Derived.RegularCauchyLipschitzMapUp
