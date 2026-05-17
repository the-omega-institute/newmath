import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ResearchProgrammeExecutionGateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ResearchProgrammeExecutionGateUp : Type where
  | mk (T P D S F B R H C Q N : BHist) : ResearchProgrammeExecutionGateUp
  deriving DecidableEq

def researchProgrammeExecutionGateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: researchProgrammeExecutionGateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: researchProgrammeExecutionGateEncodeBHist h

def researchProgrammeExecutionGateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (researchProgrammeExecutionGateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (researchProgrammeExecutionGateDecodeBHist tail)

private theorem researchProgrammeExecutionGateDecodeEncodeBHist :
    ∀ h : BHist,
      researchProgrammeExecutionGateDecodeBHist
        (researchProgrammeExecutionGateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem researchProgrammeExecutionGate_mk_congr
    {T T' P P' D D' S S' F F' B B' R R' H H' C C' Q Q' N N' : BHist}
    (hT : T' = T) (hP : P' = P) (hD : D' = D) (hS : S' = S) (hF : F' = F)
    (hB : B' = B) (hR : R' = R) (hH : H' = H) (hC : C' = C) (hQ : Q' = Q)
    (hN : N' = N) :
    ResearchProgrammeExecutionGateUp.mk T' P' D' S' F' B' R' H' C' Q' N' =
      ResearchProgrammeExecutionGateUp.mk T P D S F B R H C Q N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hT
  cases hP
  cases hD
  cases hS
  cases hF
  cases hB
  cases hR
  cases hH
  cases hC
  cases hQ
  cases hN
  rfl

def researchProgrammeExecutionGateFields :
    ResearchProgrammeExecutionGateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ResearchProgrammeExecutionGateUp.mk T P D S F B R H C Q N =>
      [T, P, D, S, F, B, R, H, C, Q, N]

def researchProgrammeExecutionGateToEventFlow :
    ResearchProgrammeExecutionGateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (researchProgrammeExecutionGateFields x).map
        researchProgrammeExecutionGateEncodeBHist

def researchProgrammeExecutionGateFromEventFlow :
    EventFlow → Option ResearchProgrammeExecutionGateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _T :: [] => none
  | _T :: _P :: [] => none
  | _T :: _P :: _D :: [] => none
  | _T :: _P :: _D :: _S :: [] => none
  | _T :: _P :: _D :: _S :: _F :: [] => none
  | _T :: _P :: _D :: _S :: _F :: _B :: [] => none
  | _T :: _P :: _D :: _S :: _F :: _B :: _R :: [] => none
  | _T :: _P :: _D :: _S :: _F :: _B :: _R :: _H :: [] => none
  | _T :: _P :: _D :: _S :: _F :: _B :: _R :: _H :: _C :: [] => none
  | _T :: _P :: _D :: _S :: _F :: _B :: _R :: _H :: _C :: _Q :: [] => none
  | T :: P :: D :: S :: F :: B :: R :: H :: C :: Q :: N :: [] =>
      some
        (ResearchProgrammeExecutionGateUp.mk
          (researchProgrammeExecutionGateDecodeBHist T)
          (researchProgrammeExecutionGateDecodeBHist P)
          (researchProgrammeExecutionGateDecodeBHist D)
          (researchProgrammeExecutionGateDecodeBHist S)
          (researchProgrammeExecutionGateDecodeBHist F)
          (researchProgrammeExecutionGateDecodeBHist B)
          (researchProgrammeExecutionGateDecodeBHist R)
          (researchProgrammeExecutionGateDecodeBHist H)
          (researchProgrammeExecutionGateDecodeBHist C)
          (researchProgrammeExecutionGateDecodeBHist Q)
          (researchProgrammeExecutionGateDecodeBHist N))
  | _T :: _P :: _D :: _S :: _F :: _B :: _R :: _H :: _C :: _Q :: _N ::
      _extra :: _rest => none

theorem ResearchProgrammeExecutionGateTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ResearchProgrammeExecutionGateUp,
      researchProgrammeExecutionGateFromEventFlow
        (researchProgrammeExecutionGateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T P D S F B R H C Q N =>
      exact
        congrArg some
          (researchProgrammeExecutionGate_mk_congr
            (researchProgrammeExecutionGateDecodeEncodeBHist T)
            (researchProgrammeExecutionGateDecodeEncodeBHist P)
            (researchProgrammeExecutionGateDecodeEncodeBHist D)
            (researchProgrammeExecutionGateDecodeEncodeBHist S)
            (researchProgrammeExecutionGateDecodeEncodeBHist F)
            (researchProgrammeExecutionGateDecodeEncodeBHist B)
            (researchProgrammeExecutionGateDecodeEncodeBHist R)
            (researchProgrammeExecutionGateDecodeEncodeBHist H)
            (researchProgrammeExecutionGateDecodeEncodeBHist C)
            (researchProgrammeExecutionGateDecodeEncodeBHist Q)
            (researchProgrammeExecutionGateDecodeEncodeBHist N))

private theorem researchProgrammeExecutionGateToEventFlow_injective
    {x y : ResearchProgrammeExecutionGateUp} :
    researchProgrammeExecutionGateToEventFlow x =
        researchProgrammeExecutionGateToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      researchProgrammeExecutionGateFromEventFlow
          (researchProgrammeExecutionGateToEventFlow x) =
        researchProgrammeExecutionGateFromEventFlow
          (researchProgrammeExecutionGateToEventFlow y) :=
    congrArg researchProgrammeExecutionGateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ResearchProgrammeExecutionGateTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ResearchProgrammeExecutionGateTasteGate_single_carrier_alignment_round_trip y)))

private theorem researchProgrammeExecutionGate_fields_faithful :
    ∀ x y : ResearchProgrammeExecutionGateUp,
      researchProgrammeExecutionGateFields x = researchProgrammeExecutionGateFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T₁ P₁ D₁ S₁ F₁ B₁ R₁ H₁ C₁ Q₁ N₁ =>
      cases y with
      | mk T₂ P₂ D₂ S₂ F₂ B₂ R₂ H₂ C₂ Q₂ N₂ =>
          cases hfields
          rfl

instance researchProgrammeExecutionGateBHistCarrier :
    BHistCarrier ResearchProgrammeExecutionGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := researchProgrammeExecutionGateToEventFlow
  fromEventFlow := researchProgrammeExecutionGateFromEventFlow

instance researchProgrammeExecutionGateChapterTasteGate :
    ChapterTasteGate ResearchProgrammeExecutionGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      researchProgrammeExecutionGateFromEventFlow
        (researchProgrammeExecutionGateToEventFlow x) = some x
    exact ResearchProgrammeExecutionGateTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (researchProgrammeExecutionGateToEventFlow_injective heq)

instance researchProgrammeExecutionGateFieldFaithful :
    FieldFaithful ResearchProgrammeExecutionGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := researchProgrammeExecutionGateFields
  field_faithful := researchProgrammeExecutionGate_fields_faithful

instance researchProgrammeExecutionGateNontrivial :
    Nontrivial ResearchProgrammeExecutionGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ResearchProgrammeExecutionGateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ResearchProgrammeExecutionGateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

end BEDC.Derived.ResearchProgrammeExecutionGateUp
