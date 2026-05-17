import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundaryAdmissionDecisionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundaryAdmissionDecisionUp : Type where
  | mk (X F R A H C P N : BHist) : BoundaryAdmissionDecisionUp
  deriving DecidableEq

def boundaryAdmissionDecisionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundaryAdmissionDecisionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundaryAdmissionDecisionEncodeBHist h

def boundaryAdmissionDecisionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundaryAdmissionDecisionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundaryAdmissionDecisionDecodeBHist tail)

private theorem boundaryAdmissionDecisionDecode_encode_bhist :
    ∀ h : BHist,
      boundaryAdmissionDecisionDecodeBHist (boundaryAdmissionDecisionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def boundaryAdmissionDecisionFields : BoundaryAdmissionDecisionUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BoundaryAdmissionDecisionUp.mk X F R A H C P N =>
      [X, F, R, A, H, C, P, N]

def boundaryAdmissionDecisionToEventFlow :
    BoundaryAdmissionDecisionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BoundaryAdmissionDecisionUp.mk X F R A H C P N =>
      [boundaryAdmissionDecisionEncodeBHist X,
        boundaryAdmissionDecisionEncodeBHist F,
        boundaryAdmissionDecisionEncodeBHist R,
        boundaryAdmissionDecisionEncodeBHist A,
        boundaryAdmissionDecisionEncodeBHist H,
        boundaryAdmissionDecisionEncodeBHist C,
        boundaryAdmissionDecisionEncodeBHist P,
        boundaryAdmissionDecisionEncodeBHist N]

def boundaryAdmissionDecisionFromEventFlow :
    EventFlow → Option BoundaryAdmissionDecisionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | X :: F :: R :: A :: H :: C :: P :: N :: [] =>
      some
        (BoundaryAdmissionDecisionUp.mk
          (boundaryAdmissionDecisionDecodeBHist X)
          (boundaryAdmissionDecisionDecodeBHist F)
          (boundaryAdmissionDecisionDecodeBHist R)
          (boundaryAdmissionDecisionDecodeBHist A)
          (boundaryAdmissionDecisionDecodeBHist H)
          (boundaryAdmissionDecisionDecodeBHist C)
          (boundaryAdmissionDecisionDecodeBHist P)
          (boundaryAdmissionDecisionDecodeBHist N))
  | _ => none

private theorem boundaryAdmissionDecision_round_trip :
    ∀ x : BoundaryAdmissionDecisionUp,
      boundaryAdmissionDecisionFromEventFlow
          (boundaryAdmissionDecisionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X F R A H C P N =>
      simp only [boundaryAdmissionDecisionToEventFlow,
        boundaryAdmissionDecisionFromEventFlow,
        boundaryAdmissionDecisionDecode_encode_bhist]

private theorem boundaryAdmissionDecisionToEventFlow_injective
    {x y : BoundaryAdmissionDecisionUp} :
    boundaryAdmissionDecisionToEventFlow x =
        boundaryAdmissionDecisionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          boundaryAdmissionDecisionFromEventFlow
            (boundaryAdmissionDecisionToEventFlow x) :=
        (boundaryAdmissionDecision_round_trip x).symm
      _ =
          boundaryAdmissionDecisionFromEventFlow
            (boundaryAdmissionDecisionToEventFlow y) :=
        congrArg boundaryAdmissionDecisionFromEventFlow hxy
      _ = some y := boundaryAdmissionDecision_round_trip y
  exact Option.some.inj optionEq

private theorem boundaryAdmissionDecision_field_faithful :
    ∀ x y : BoundaryAdmissionDecisionUp,
      boundaryAdmissionDecisionFields x = boundaryAdmissionDecisionFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk X1 F1 R1 A1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 F2 R2 A2 H2 C2 P2 N2 =>
          cases h
          rfl

instance boundaryAdmissionDecisionBHistCarrier :
    BHistCarrier BoundaryAdmissionDecisionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundaryAdmissionDecisionToEventFlow
  fromEventFlow := boundaryAdmissionDecisionFromEventFlow

instance boundaryAdmissionDecisionChapterTasteGate :
    ChapterTasteGate BoundaryAdmissionDecisionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      boundaryAdmissionDecisionFromEventFlow
          (boundaryAdmissionDecisionToEventFlow x) =
        some x
    exact boundaryAdmissionDecision_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (boundaryAdmissionDecisionToEventFlow_injective heq)

instance boundaryAdmissionDecisionFieldFaithful :
    FieldFaithful BoundaryAdmissionDecisionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := boundaryAdmissionDecisionFields
  field_faithful := boundaryAdmissionDecision_field_faithful

instance boundaryAdmissionDecisionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BoundaryAdmissionDecisionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundaryAdmissionDecisionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BoundaryAdmissionDecisionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BoundaryAdmissionDecisionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  boundaryAdmissionDecisionChapterTasteGate

end BEDC.Derived.BoundaryAdmissionDecisionUp
