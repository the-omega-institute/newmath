import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CurvatureUp : Type where
  | mk : (curvature deRham provenance connectionLedger classRow : BHist) → CurvatureUp
  deriving DecidableEq

def CurvatureTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: CurvatureTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: CurvatureTasteGate_single_carrier_alignment_encodeBHist h

def CurvatureTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (CurvatureTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (CurvatureTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CurvatureTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      CurvatureTasteGate_single_carrier_alignment_decodeBHist
        (CurvatureTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def CurvatureTasteGate_single_carrier_alignment_fields : CurvatureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CurvatureUp.mk curvature deRham provenance connectionLedger classRow =>
      [curvature, deRham, provenance, connectionLedger, classRow]

def CurvatureTasteGate_single_carrier_alignment_toEventFlow : CurvatureUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (CurvatureTasteGate_single_carrier_alignment_fields x).map
        CurvatureTasteGate_single_carrier_alignment_encodeBHist

def CurvatureTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option CurvatureUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | curvature :: rest0 =>
      match rest0 with
      | [] => none
      | deRham :: rest1 =>
          match rest1 with
          | [] => none
          | provenance :: rest2 =>
              match rest2 with
              | [] => none
              | connectionLedger :: rest3 =>
                  match rest3 with
                  | [] => none
                  | classRow :: rest4 =>
                      match rest4 with
                      | [] =>
                          some
                            (CurvatureUp.mk
                              (CurvatureTasteGate_single_carrier_alignment_decodeBHist curvature)
                              (CurvatureTasteGate_single_carrier_alignment_decodeBHist deRham)
                              (CurvatureTasteGate_single_carrier_alignment_decodeBHist provenance)
                              (CurvatureTasteGate_single_carrier_alignment_decodeBHist
                                connectionLedger)
                              (CurvatureTasteGate_single_carrier_alignment_decodeBHist classRow))
                      | _ :: _ => none

private theorem CurvatureTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CurvatureUp,
      CurvatureTasteGate_single_carrier_alignment_fromEventFlow
        (CurvatureTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk curvature deRham provenance connectionLedger classRow =>
      change
        some
          (CurvatureUp.mk
            (CurvatureTasteGate_single_carrier_alignment_decodeBHist
              (CurvatureTasteGate_single_carrier_alignment_encodeBHist curvature))
            (CurvatureTasteGate_single_carrier_alignment_decodeBHist
              (CurvatureTasteGate_single_carrier_alignment_encodeBHist deRham))
            (CurvatureTasteGate_single_carrier_alignment_decodeBHist
              (CurvatureTasteGate_single_carrier_alignment_encodeBHist provenance))
            (CurvatureTasteGate_single_carrier_alignment_decodeBHist
              (CurvatureTasteGate_single_carrier_alignment_encodeBHist connectionLedger))
            (CurvatureTasteGate_single_carrier_alignment_decodeBHist
              (CurvatureTasteGate_single_carrier_alignment_encodeBHist classRow))) =
          some (CurvatureUp.mk curvature deRham provenance connectionLedger classRow)
      rw [CurvatureTasteGate_single_carrier_alignment_decode_encode curvature,
        CurvatureTasteGate_single_carrier_alignment_decode_encode deRham,
        CurvatureTasteGate_single_carrier_alignment_decode_encode provenance,
        CurvatureTasteGate_single_carrier_alignment_decode_encode connectionLedger,
        CurvatureTasteGate_single_carrier_alignment_decode_encode classRow]

private theorem CurvatureTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CurvatureUp} :
    CurvatureTasteGate_single_carrier_alignment_toEventFlow x =
      CurvatureTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      CurvatureTasteGate_single_carrier_alignment_fromEventFlow
          (CurvatureTasteGate_single_carrier_alignment_toEventFlow x) =
        CurvatureTasteGate_single_carrier_alignment_fromEventFlow
          (CurvatureTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg CurvatureTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CurvatureTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CurvatureTasteGate_single_carrier_alignment_round_trip y)))

private theorem CurvatureTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : CurvatureUp,
      CurvatureTasteGate_single_carrier_alignment_fields x =
        CurvatureTasteGate_single_carrier_alignment_fields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk curvature₁ deRham₁ provenance₁ connectionLedger₁ classRow₁ =>
      cases y with
      | mk curvature₂ deRham₂ provenance₂ connectionLedger₂ classRow₂ =>
          injection h with hCurvature t1
          injection t1 with hDeRham t2
          injection t2 with hProvenance t3
          injection t3 with hConnectionLedger t4
          injection t4 with hClassRow _
          subst hCurvature
          subst hDeRham
          subst hProvenance
          subst hConnectionLedger
          subst hClassRow
          rfl

instance curvatureBHistCarrier : BHistCarrier CurvatureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CurvatureTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CurvatureTasteGate_single_carrier_alignment_fromEventFlow

instance curvatureChapterTasteGate : ChapterTasteGate CurvatureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CurvatureTasteGate_single_carrier_alignment_fromEventFlow
          (CurvatureTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact CurvatureTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CurvatureTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance curvatureFieldFaithful : FieldFaithful CurvatureUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := CurvatureTasteGate_single_carrier_alignment_fields
  field_faithful := CurvatureTasteGate_single_carrier_alignment_field_faithful

instance curvatureNontrivial : Nontrivial CurvatureUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CurvatureUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CurvatureUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CurvatureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  curvatureChapterTasteGate

theorem CurvatureTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CurvatureUp) ∧ Nonempty (ChapterTasteGate CurvatureUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨curvatureBHistCarrier⟩
  · exact ⟨curvatureChapterTasteGate⟩

end BEDC.Derived.CurvatureUp
