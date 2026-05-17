import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TypedFailureCertificateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TypedFailureCertificateUp : Type where
  | mk :
      (objectName theoryGrade formalStatus failedSite refusalRoute diagnosticBranch transport
        provenance localName : BHist) →
        TypedFailureCertificateUp
  deriving DecidableEq

def typedFailureCertificateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: typedFailureCertificateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: typedFailureCertificateEncodeBHist h

def typedFailureCertificateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (typedFailureCertificateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (typedFailureCertificateDecodeBHist tail)

private theorem typedFailureCertificateDecodeEncodeBHist :
    ∀ h : BHist,
      typedFailureCertificateDecodeBHist
        (typedFailureCertificateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def typedFailureCertificateFields : TypedFailureCertificateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TypedFailureCertificateUp.mk objectName theoryGrade formalStatus failedSite refusalRoute
      diagnosticBranch transport provenance localName =>
      [objectName, theoryGrade, formalStatus, failedSite, refusalRoute, diagnosticBranch,
        transport, provenance, localName]

def typedFailureCertificateToEventFlow : TypedFailureCertificateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (typedFailureCertificateFields x).map typedFailureCertificateEncodeBHist

def typedFailureCertificateFromEventFlow :
    EventFlow → Option TypedFailureCertificateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | objectName :: rest0 =>
      match rest0 with
      | [] => none
      | theoryGrade :: rest1 =>
          match rest1 with
          | [] => none
          | formalStatus :: rest2 =>
              match rest2 with
              | [] => none
              | failedSite :: rest3 =>
                  match rest3 with
                  | [] => none
                  | refusalRoute :: rest4 =>
                      match rest4 with
                      | [] => none
                      | diagnosticBranch :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | localName :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (TypedFailureCertificateUp.mk
                                              (typedFailureCertificateDecodeBHist objectName)
                                              (typedFailureCertificateDecodeBHist theoryGrade)
                                              (typedFailureCertificateDecodeBHist formalStatus)
                                              (typedFailureCertificateDecodeBHist failedSite)
                                              (typedFailureCertificateDecodeBHist refusalRoute)
                                              (typedFailureCertificateDecodeBHist
                                                diagnosticBranch)
                                              (typedFailureCertificateDecodeBHist transport)
                                              (typedFailureCertificateDecodeBHist provenance)
                                              (typedFailureCertificateDecodeBHist localName))
                                      | _ :: _ => none

private theorem typedFailureCertificate_round_trip :
    ∀ x : TypedFailureCertificateUp,
      typedFailureCertificateFromEventFlow
        (typedFailureCertificateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk objectName theoryGrade formalStatus failedSite refusalRoute diagnosticBranch transport
      provenance localName =>
      change
        some
          (TypedFailureCertificateUp.mk
            (typedFailureCertificateDecodeBHist
              (typedFailureCertificateEncodeBHist objectName))
            (typedFailureCertificateDecodeBHist
              (typedFailureCertificateEncodeBHist theoryGrade))
            (typedFailureCertificateDecodeBHist
              (typedFailureCertificateEncodeBHist formalStatus))
            (typedFailureCertificateDecodeBHist
              (typedFailureCertificateEncodeBHist failedSite))
            (typedFailureCertificateDecodeBHist
              (typedFailureCertificateEncodeBHist refusalRoute))
            (typedFailureCertificateDecodeBHist
              (typedFailureCertificateEncodeBHist diagnosticBranch))
            (typedFailureCertificateDecodeBHist
              (typedFailureCertificateEncodeBHist transport))
            (typedFailureCertificateDecodeBHist
              (typedFailureCertificateEncodeBHist provenance))
            (typedFailureCertificateDecodeBHist
              (typedFailureCertificateEncodeBHist localName))) =
          some
            (TypedFailureCertificateUp.mk objectName theoryGrade formalStatus failedSite
              refusalRoute diagnosticBranch transport provenance localName)
      rw [typedFailureCertificateDecodeEncodeBHist objectName,
        typedFailureCertificateDecodeEncodeBHist theoryGrade,
        typedFailureCertificateDecodeEncodeBHist formalStatus,
        typedFailureCertificateDecodeEncodeBHist failedSite,
        typedFailureCertificateDecodeEncodeBHist refusalRoute,
        typedFailureCertificateDecodeEncodeBHist diagnosticBranch,
        typedFailureCertificateDecodeEncodeBHist transport,
        typedFailureCertificateDecodeEncodeBHist provenance,
        typedFailureCertificateDecodeEncodeBHist localName]

private theorem typedFailureCertificateToEventFlow_injective
    {x y : TypedFailureCertificateUp} :
    typedFailureCertificateToEventFlow x =
      typedFailureCertificateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      typedFailureCertificateFromEventFlow (typedFailureCertificateToEventFlow x) =
        typedFailureCertificateFromEventFlow (typedFailureCertificateToEventFlow y) :=
    congrArg typedFailureCertificateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (typedFailureCertificate_round_trip x).symm
      (Eq.trans hread (typedFailureCertificate_round_trip y)))

private theorem typedFailureCertificate_fields_faithful :
    ∀ x y : TypedFailureCertificateUp,
      typedFailureCertificateFields x = typedFailureCertificateFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk objectName₁ theoryGrade₁ formalStatus₁ failedSite₁ refusalRoute₁ diagnosticBranch₁
      transport₁ provenance₁ localName₁ =>
      cases y with
      | mk objectName₂ theoryGrade₂ formalStatus₂ failedSite₂ refusalRoute₂ diagnosticBranch₂
          transport₂ provenance₂ localName₂ =>
          injection hfields with hobjectName tail0
          injection tail0 with htheoryGrade tail1
          injection tail1 with hformalStatus tail2
          injection tail2 with hfailedSite tail3
          injection tail3 with hrefusalRoute tail4
          injection tail4 with hdiagnosticBranch tail5
          injection tail5 with htransport tail6
          injection tail6 with hprovenance tail7
          injection tail7 with hlocalName _
          subst hobjectName
          subst htheoryGrade
          subst hformalStatus
          subst hfailedSite
          subst hrefusalRoute
          subst hdiagnosticBranch
          subst htransport
          subst hprovenance
          subst hlocalName
          rfl

instance typedFailureCertificateBHistCarrier :
    BHistCarrier TypedFailureCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := typedFailureCertificateToEventFlow
  fromEventFlow := typedFailureCertificateFromEventFlow

instance typedFailureCertificateChapterTasteGate :
    ChapterTasteGate TypedFailureCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      typedFailureCertificateFromEventFlow
        (typedFailureCertificateToEventFlow x) = some x
    exact typedFailureCertificate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (typedFailureCertificateToEventFlow_injective heq)

instance typedFailureCertificateFieldFaithful :
    FieldFaithful TypedFailureCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := typedFailureCertificateFields
  field_faithful := typedFailureCertificate_fields_faithful

instance typedFailureCertificateNontrivial : Nontrivial TypedFailureCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TypedFailureCertificateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TypedFailureCertificateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate TypedFailureCertificateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  typedFailureCertificateChapterTasteGate

theorem TypedFailureCertificateTasteGate_single_carrier_alignment :
    (∀ h : BHist, typedFailureCertificateDecodeBHist
      (typedFailureCertificateEncodeBHist h) = h) ∧
      (∀ x : TypedFailureCertificateUp,
        typedFailureCertificateFromEventFlow
          (typedFailureCertificateToEventFlow x) = some x) ∧
        (∀ x y : TypedFailureCertificateUp,
          typedFailureCertificateToEventFlow x =
            typedFailureCertificateToEventFlow y → x = y) ∧
          typedFailureCertificateEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : TypedFailureCertificateUp,
              typedFailureCertificateFields x = typedFailureCertificateFields y → x = y) ∧
              (∃ x y : TypedFailureCertificateUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact typedFailureCertificateDecodeEncodeBHist
  · constructor
    · exact typedFailureCertificate_round_trip
    · constructor
      · intro x y heq
        exact typedFailureCertificateToEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · exact typedFailureCertificate_fields_faithful
          · exact
              ⟨TypedFailureCertificateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                TypedFailureCertificateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                by
                  intro h
                  cases h⟩

end BEDC.Derived.TypedFailureCertificateUp
