import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionStrengthUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionStrengthUp : Type where
  | mk :
      (sourceLeft sourceRight windowLeft windowRight dyadicLeft dyadicRight productRoute
        completionHandoff realSeal exactness transport replay provenance localName : BHist) →
        CauchyCompletionStrengthUp
  deriving DecidableEq

def cauchyCompletionStrengthEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionStrengthEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionStrengthEncodeBHist h

def cauchyCompletionStrengthDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionStrengthDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionStrengthDecodeBHist tail)

private theorem CauchyCompletionStrengthTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyCompletionStrengthDecodeBHist (cauchyCompletionStrengthEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CauchyCompletionStrengthTasteGate_single_carrier_alignment_fields :
    CauchyCompletionStrengthUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionStrengthUp.mk sourceLeft sourceRight windowLeft windowRight dyadicLeft
      dyadicRight productRoute completionHandoff realSeal exactness transport replay provenance
      localName =>
      [sourceLeft, sourceRight, windowLeft, windowRight, dyadicLeft, dyadicRight, productRoute,
        completionHandoff, realSeal, exactness, transport, replay, provenance, localName]

def CauchyCompletionStrengthTasteGate_single_carrier_alignment_toEventFlow :
    CauchyCompletionStrengthUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (CauchyCompletionStrengthTasteGate_single_carrier_alignment_fields x).map
      cauchyCompletionStrengthEncodeBHist

def CauchyCompletionStrengthTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option CauchyCompletionStrengthUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun eventFlow =>
    match eventFlow with
    | sourceLeft :: sourceRight :: windowLeft :: windowRight :: dyadicLeft :: dyadicRight ::
        productRoute :: completionHandoff :: realSeal :: exactness :: transport :: replay ::
          provenance :: localName :: [] =>
        some
          (CauchyCompletionStrengthUp.mk
            (cauchyCompletionStrengthDecodeBHist sourceLeft)
            (cauchyCompletionStrengthDecodeBHist sourceRight)
            (cauchyCompletionStrengthDecodeBHist windowLeft)
            (cauchyCompletionStrengthDecodeBHist windowRight)
            (cauchyCompletionStrengthDecodeBHist dyadicLeft)
            (cauchyCompletionStrengthDecodeBHist dyadicRight)
            (cauchyCompletionStrengthDecodeBHist productRoute)
            (cauchyCompletionStrengthDecodeBHist completionHandoff)
            (cauchyCompletionStrengthDecodeBHist realSeal)
            (cauchyCompletionStrengthDecodeBHist exactness)
            (cauchyCompletionStrengthDecodeBHist transport)
            (cauchyCompletionStrengthDecodeBHist replay)
            (cauchyCompletionStrengthDecodeBHist provenance)
            (cauchyCompletionStrengthDecodeBHist localName))
    | _ => none

private theorem CauchyCompletionStrengthTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCompletionStrengthUp,
      CauchyCompletionStrengthTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyCompletionStrengthTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceLeft sourceRight windowLeft windowRight dyadicLeft dyadicRight productRoute
      completionHandoff realSeal exactness transport replay provenance localName =>
      change
        some
            (CauchyCompletionStrengthUp.mk
              (cauchyCompletionStrengthDecodeBHist
                (cauchyCompletionStrengthEncodeBHist sourceLeft))
              (cauchyCompletionStrengthDecodeBHist
                (cauchyCompletionStrengthEncodeBHist sourceRight))
              (cauchyCompletionStrengthDecodeBHist
                (cauchyCompletionStrengthEncodeBHist windowLeft))
              (cauchyCompletionStrengthDecodeBHist
                (cauchyCompletionStrengthEncodeBHist windowRight))
              (cauchyCompletionStrengthDecodeBHist
                (cauchyCompletionStrengthEncodeBHist dyadicLeft))
              (cauchyCompletionStrengthDecodeBHist
                (cauchyCompletionStrengthEncodeBHist dyadicRight))
              (cauchyCompletionStrengthDecodeBHist
                (cauchyCompletionStrengthEncodeBHist productRoute))
              (cauchyCompletionStrengthDecodeBHist
                (cauchyCompletionStrengthEncodeBHist completionHandoff))
              (cauchyCompletionStrengthDecodeBHist
                (cauchyCompletionStrengthEncodeBHist realSeal))
              (cauchyCompletionStrengthDecodeBHist
                (cauchyCompletionStrengthEncodeBHist exactness))
              (cauchyCompletionStrengthDecodeBHist
                (cauchyCompletionStrengthEncodeBHist transport))
              (cauchyCompletionStrengthDecodeBHist
                (cauchyCompletionStrengthEncodeBHist replay))
              (cauchyCompletionStrengthDecodeBHist
                (cauchyCompletionStrengthEncodeBHist provenance))
              (cauchyCompletionStrengthDecodeBHist
                (cauchyCompletionStrengthEncodeBHist localName))) =
          some
            (CauchyCompletionStrengthUp.mk sourceLeft sourceRight windowLeft windowRight
              dyadicLeft dyadicRight productRoute completionHandoff realSeal exactness transport
              replay provenance localName)
      rw [CauchyCompletionStrengthTasteGate_single_carrier_alignment_decode_encode sourceLeft]
      rw [CauchyCompletionStrengthTasteGate_single_carrier_alignment_decode_encode sourceRight]
      rw [CauchyCompletionStrengthTasteGate_single_carrier_alignment_decode_encode windowLeft]
      rw [CauchyCompletionStrengthTasteGate_single_carrier_alignment_decode_encode windowRight]
      rw [CauchyCompletionStrengthTasteGate_single_carrier_alignment_decode_encode dyadicLeft]
      rw [CauchyCompletionStrengthTasteGate_single_carrier_alignment_decode_encode dyadicRight]
      rw [CauchyCompletionStrengthTasteGate_single_carrier_alignment_decode_encode productRoute]
      rw [CauchyCompletionStrengthTasteGate_single_carrier_alignment_decode_encode
        completionHandoff]
      rw [CauchyCompletionStrengthTasteGate_single_carrier_alignment_decode_encode realSeal]
      rw [CauchyCompletionStrengthTasteGate_single_carrier_alignment_decode_encode exactness]
      rw [CauchyCompletionStrengthTasteGate_single_carrier_alignment_decode_encode transport]
      rw [CauchyCompletionStrengthTasteGate_single_carrier_alignment_decode_encode replay]
      rw [CauchyCompletionStrengthTasteGate_single_carrier_alignment_decode_encode provenance]
      rw [CauchyCompletionStrengthTasteGate_single_carrier_alignment_decode_encode localName]

private theorem CauchyCompletionStrengthTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCompletionStrengthUp} :
    CauchyCompletionStrengthTasteGate_single_carrier_alignment_toEventFlow x =
        CauchyCompletionStrengthTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      CauchyCompletionStrengthTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyCompletionStrengthTasteGate_single_carrier_alignment_toEventFlow x) =
        CauchyCompletionStrengthTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyCompletionStrengthTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg CauchyCompletionStrengthTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyCompletionStrengthTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletionStrengthTasteGate_single_carrier_alignment_round_trip y)))

instance CauchyCompletionStrengthTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier CauchyCompletionStrengthUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CauchyCompletionStrengthTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CauchyCompletionStrengthTasteGate_single_carrier_alignment_fromEventFlow

instance CauchyCompletionStrengthTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate CauchyCompletionStrengthUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CauchyCompletionStrengthTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyCompletionStrengthTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact CauchyCompletionStrengthTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact
      hxy (CauchyCompletionStrengthTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def CauchyCompletionStrengthTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CauchyCompletionStrengthUp :=
  -- BEDC touchpoint anchor: BHist BMark
  CauchyCompletionStrengthTasteGate_single_carrier_alignment_ChapterTasteGate

theorem CauchyCompletionStrengthTasteGate_single_carrier_alignment :
    (forall h : BHist,
      cauchyCompletionStrengthDecodeBHist (cauchyCompletionStrengthEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyCompletionStrengthUp) ∧
        Nonempty (ChapterTasteGate CauchyCompletionStrengthUp) ∧
          cauchyCompletionStrengthEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyCompletionStrengthTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨CauchyCompletionStrengthTasteGate_single_carrier_alignment_BHistCarrier⟩,
        ⟨⟨CauchyCompletionStrengthTasteGate_single_carrier_alignment_ChapterTasteGate⟩,
          rfl⟩⟩⟩

end BEDC.Derived.CauchyCompletionStrengthUp
