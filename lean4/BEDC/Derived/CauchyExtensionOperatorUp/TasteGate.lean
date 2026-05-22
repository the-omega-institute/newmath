import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyExtensionOperatorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyExtensionOperatorUp : Type where
  | mk :
      (source window tolerance map extension sealRow transport replay provenance
        localCert : BHist) →
        CauchyExtensionOperatorUp
  deriving DecidableEq

def cauchyExtensionOperatorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyExtensionOperatorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyExtensionOperatorEncodeBHist h

def cauchyExtensionOperatorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyExtensionOperatorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyExtensionOperatorDecodeBHist tail)

private theorem cauchyExtensionOperator_decode_encode :
    ∀ h : BHist,
      cauchyExtensionOperatorDecodeBHist (cauchyExtensionOperatorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyExtensionOperatorFields : CauchyExtensionOperatorUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | CauchyExtensionOperatorUp.mk source window tolerance map extension sealRow transport replay
      provenance localCert =>
      [source, window, tolerance, map, extension, sealRow, transport, replay, provenance,
        localCert]

def cauchyExtensionOperatorToEventFlow : CauchyExtensionOperatorUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchyExtensionOperatorFields x).map cauchyExtensionOperatorEncodeBHist

def cauchyExtensionOperatorFromEventFlow :
    EventFlow → Option CauchyExtensionOperatorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | source :: window :: tolerance :: map :: extension :: sealRow :: transport :: replay ::
      provenance :: localCert :: [] =>
      some
        (CauchyExtensionOperatorUp.mk
          (cauchyExtensionOperatorDecodeBHist source)
          (cauchyExtensionOperatorDecodeBHist window)
          (cauchyExtensionOperatorDecodeBHist tolerance)
          (cauchyExtensionOperatorDecodeBHist map)
          (cauchyExtensionOperatorDecodeBHist extension)
          (cauchyExtensionOperatorDecodeBHist sealRow)
          (cauchyExtensionOperatorDecodeBHist transport)
          (cauchyExtensionOperatorDecodeBHist replay)
          (cauchyExtensionOperatorDecodeBHist provenance)
          (cauchyExtensionOperatorDecodeBHist localCert))
  | _ => none

private theorem cauchyExtensionOperator_round_trip :
    ∀ x : CauchyExtensionOperatorUp,
      cauchyExtensionOperatorFromEventFlow (cauchyExtensionOperatorToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk source window tolerance map extension sealRow transport replay provenance localCert =>
      simp only [cauchyExtensionOperatorToEventFlow, cauchyExtensionOperatorFields,
        cauchyExtensionOperatorFromEventFlow, List.map_cons, List.map_nil,
        cauchyExtensionOperator_decode_encode]

private theorem cauchyExtensionOperatorToEventFlow_injective
    {x y : CauchyExtensionOperatorUp} :
    cauchyExtensionOperatorToEventFlow x = cauchyExtensionOperatorToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          cauchyExtensionOperatorFromEventFlow (cauchyExtensionOperatorToEventFlow x) :=
        (cauchyExtensionOperator_round_trip x).symm
      _ = cauchyExtensionOperatorFromEventFlow (cauchyExtensionOperatorToEventFlow y) :=
        congrArg cauchyExtensionOperatorFromEventFlow hxy
      _ = some y := cauchyExtensionOperator_round_trip y
  exact Option.some.inj optionEq

instance cauchyExtensionOperatorBHistCarrier : BHistCarrier CauchyExtensionOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyExtensionOperatorToEventFlow
  fromEventFlow := cauchyExtensionOperatorFromEventFlow

instance cauchyExtensionOperatorChapterTasteGate :
    ChapterTasteGate CauchyExtensionOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyExtensionOperatorFromEventFlow (cauchyExtensionOperatorToEventFlow x) =
      some x
    exact cauchyExtensionOperator_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyExtensionOperatorToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyExtensionOperatorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyExtensionOperatorChapterTasteGate

end BEDC.Derived.CauchyExtensionOperatorUp
