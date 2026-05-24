import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompletionExtensionUniquenessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompletionExtensionUniquenessUp : Type where
  | mk :
      (sourceCompletion denseRoute extensionHandoff universalRow completeTarget
        separatedTarget uniquenessLedger transport replay provenance localName : BHist) →
        CompletionExtensionUniquenessUp
  deriving DecidableEq

def completionExtensionUniquenessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completionExtensionUniquenessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completionExtensionUniquenessEncodeBHist h

def completionExtensionUniquenessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completionExtensionUniquenessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completionExtensionUniquenessDecodeBHist tail)

private theorem CompletionExtensionUniquenessTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      completionExtensionUniquenessDecodeBHist
        (completionExtensionUniquenessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def completionExtensionUniquenessFields : CompletionExtensionUniquenessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompletionExtensionUniquenessUp.mk sourceCompletion denseRoute extensionHandoff
      universalRow completeTarget separatedTarget uniquenessLedger transport replay provenance
      localName =>
      [sourceCompletion, denseRoute, extensionHandoff, universalRow, completeTarget,
        separatedTarget, uniquenessLedger, transport, replay, provenance, localName]

def completionExtensionUniquenessToEventFlow : CompletionExtensionUniquenessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (completionExtensionUniquenessFields x).map completionExtensionUniquenessEncodeBHist

def completionExtensionUniquenessFromEventFlow :
    EventFlow → Option CompletionExtensionUniquenessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | sourceCompletion :: rest0 =>
      match rest0 with
      | [] => none
      | denseRoute :: rest1 =>
          match rest1 with
          | [] => none
          | extensionHandoff :: rest2 =>
              match rest2 with
              | [] => none
              | universalRow :: rest3 =>
                  match rest3 with
                  | [] => none
                  | completeTarget :: rest4 =>
                      match rest4 with
                      | [] => none
                      | separatedTarget :: rest5 =>
                          match rest5 with
                          | [] => none
                          | uniquenessLedger :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | replay :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | provenance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | localName :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (CompletionExtensionUniquenessUp.mk
                                                      (completionExtensionUniquenessDecodeBHist
                                                        sourceCompletion)
                                                      (completionExtensionUniquenessDecodeBHist
                                                        denseRoute)
                                                      (completionExtensionUniquenessDecodeBHist
                                                        extensionHandoff)
                                                      (completionExtensionUniquenessDecodeBHist
                                                        universalRow)
                                                      (completionExtensionUniquenessDecodeBHist
                                                        completeTarget)
                                                      (completionExtensionUniquenessDecodeBHist
                                                        separatedTarget)
                                                      (completionExtensionUniquenessDecodeBHist
                                                        uniquenessLedger)
                                                      (completionExtensionUniquenessDecodeBHist
                                                        transport)
                                                      (completionExtensionUniquenessDecodeBHist
                                                        replay)
                                                      (completionExtensionUniquenessDecodeBHist
                                                        provenance)
                                                      (completionExtensionUniquenessDecodeBHist
                                                        localName))
                                              | _ :: _ => none

private theorem CompletionExtensionUniquenessTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompletionExtensionUniquenessUp,
      completionExtensionUniquenessFromEventFlow
        (completionExtensionUniquenessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceCompletion denseRoute extensionHandoff universalRow completeTarget separatedTarget
      uniquenessLedger transport replay provenance localName =>
      change
        some
          (CompletionExtensionUniquenessUp.mk
            (completionExtensionUniquenessDecodeBHist
              (completionExtensionUniquenessEncodeBHist sourceCompletion))
            (completionExtensionUniquenessDecodeBHist
              (completionExtensionUniquenessEncodeBHist denseRoute))
            (completionExtensionUniquenessDecodeBHist
              (completionExtensionUniquenessEncodeBHist extensionHandoff))
            (completionExtensionUniquenessDecodeBHist
              (completionExtensionUniquenessEncodeBHist universalRow))
            (completionExtensionUniquenessDecodeBHist
              (completionExtensionUniquenessEncodeBHist completeTarget))
            (completionExtensionUniquenessDecodeBHist
              (completionExtensionUniquenessEncodeBHist separatedTarget))
            (completionExtensionUniquenessDecodeBHist
              (completionExtensionUniquenessEncodeBHist uniquenessLedger))
            (completionExtensionUniquenessDecodeBHist
              (completionExtensionUniquenessEncodeBHist transport))
            (completionExtensionUniquenessDecodeBHist
              (completionExtensionUniquenessEncodeBHist replay))
            (completionExtensionUniquenessDecodeBHist
              (completionExtensionUniquenessEncodeBHist provenance))
            (completionExtensionUniquenessDecodeBHist
              (completionExtensionUniquenessEncodeBHist localName))) =
          some
            (CompletionExtensionUniquenessUp.mk sourceCompletion denseRoute extensionHandoff
              universalRow completeTarget separatedTarget uniquenessLedger transport replay
              provenance localName)
      rw [CompletionExtensionUniquenessTasteGate_single_carrier_alignment_decode
          sourceCompletion,
        CompletionExtensionUniquenessTasteGate_single_carrier_alignment_decode denseRoute,
        CompletionExtensionUniquenessTasteGate_single_carrier_alignment_decode
          extensionHandoff,
        CompletionExtensionUniquenessTasteGate_single_carrier_alignment_decode universalRow,
        CompletionExtensionUniquenessTasteGate_single_carrier_alignment_decode completeTarget,
        CompletionExtensionUniquenessTasteGate_single_carrier_alignment_decode separatedTarget,
        CompletionExtensionUniquenessTasteGate_single_carrier_alignment_decode uniquenessLedger,
        CompletionExtensionUniquenessTasteGate_single_carrier_alignment_decode transport,
        CompletionExtensionUniquenessTasteGate_single_carrier_alignment_decode replay,
        CompletionExtensionUniquenessTasteGate_single_carrier_alignment_decode provenance,
        CompletionExtensionUniquenessTasteGate_single_carrier_alignment_decode localName]

private theorem CompletionExtensionUniquenessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompletionExtensionUniquenessUp} :
    completionExtensionUniquenessToEventFlow x =
      completionExtensionUniquenessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completionExtensionUniquenessFromEventFlow
          (completionExtensionUniquenessToEventFlow x) =
        completionExtensionUniquenessFromEventFlow
          (completionExtensionUniquenessToEventFlow y) :=
    congrArg completionExtensionUniquenessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompletionExtensionUniquenessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompletionExtensionUniquenessTasteGate_single_carrier_alignment_round_trip y)))

private theorem CompletionExtensionUniquenessTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CompletionExtensionUniquenessUp,
      completionExtensionUniquenessFields x = completionExtensionUniquenessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk sourceCompletion₁ denseRoute₁ extensionHandoff₁ universalRow₁ completeTarget₁
      separatedTarget₁ uniquenessLedger₁ transport₁ replay₁ provenance₁ localName₁ =>
      cases y with
      | mk sourceCompletion₂ denseRoute₂ extensionHandoff₂ universalRow₂ completeTarget₂
          separatedTarget₂ uniquenessLedger₂ transport₂ replay₂ provenance₂ localName₂ =>
          injection hfields with hSourceCompletion tail0
          injection tail0 with hDenseRoute tail1
          injection tail1 with hExtensionHandoff tail2
          injection tail2 with hUniversalRow tail3
          injection tail3 with hCompleteTarget tail4
          injection tail4 with hSeparatedTarget tail5
          injection tail5 with hUniquenessLedger tail6
          injection tail6 with hTransport tail7
          injection tail7 with hReplay tail8
          injection tail8 with hProvenance tail9
          injection tail9 with hLocalName _
          subst hSourceCompletion
          subst hDenseRoute
          subst hExtensionHandoff
          subst hUniversalRow
          subst hCompleteTarget
          subst hSeparatedTarget
          subst hUniquenessLedger
          subst hTransport
          subst hReplay
          subst hProvenance
          subst hLocalName
          rfl

instance completionExtensionUniquenessBHistCarrier :
    BHistCarrier CompletionExtensionUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completionExtensionUniquenessToEventFlow
  fromEventFlow := completionExtensionUniquenessFromEventFlow

instance completionExtensionUniquenessChapterTasteGate :
    ChapterTasteGate CompletionExtensionUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      completionExtensionUniquenessFromEventFlow
          (completionExtensionUniquenessToEventFlow x) = some x
    exact CompletionExtensionUniquenessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompletionExtensionUniquenessTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance completionExtensionUniquenessFieldFaithful :
    FieldFaithful CompletionExtensionUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := completionExtensionUniquenessFields
  field_faithful :=
    CompletionExtensionUniquenessTasteGate_single_carrier_alignment_fields_faithful

instance completionExtensionUniquenessNontrivial : Nontrivial CompletionExtensionUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompletionExtensionUniquenessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompletionExtensionUniquenessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CompletionExtensionUniquenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  completionExtensionUniquenessChapterTasteGate

theorem CompletionExtensionUniquenessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      completionExtensionUniquenessDecodeBHist
        (completionExtensionUniquenessEncodeBHist h) = h) ∧
      (∀ x : CompletionExtensionUniquenessUp,
        completionExtensionUniquenessFromEventFlow
          (completionExtensionUniquenessToEventFlow x) = some x) ∧
        (∀ x y : CompletionExtensionUniquenessUp,
          completionExtensionUniquenessToEventFlow x =
            completionExtensionUniquenessToEventFlow y → x = y) ∧
          completionExtensionUniquenessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CompletionExtensionUniquenessTasteGate_single_carrier_alignment_decode,
      CompletionExtensionUniquenessTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CompletionExtensionUniquenessTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.CompletionExtensionUniquenessUp
