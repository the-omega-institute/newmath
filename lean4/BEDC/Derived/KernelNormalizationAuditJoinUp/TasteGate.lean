import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KernelNormalizationAuditJoinUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KernelNormalizationAuditJoinUp : Type where
  | mk
      (kernelStamp axiomQuery normalizationReplay closedNormal subjectBoundary nonescape
        routeJoin transport continuation provenance localName : BHist) :
      KernelNormalizationAuditJoinUp
  deriving DecidableEq

def kernelNormalizationAuditJoinEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kernelNormalizationAuditJoinEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kernelNormalizationAuditJoinEncodeBHist h

def kernelNormalizationAuditJoinDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kernelNormalizationAuditJoinDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kernelNormalizationAuditJoinDecodeBHist tail)

private theorem kernelNormalizationAuditJoinDecode_encode_bhist :
    ∀ h : BHist,
      kernelNormalizationAuditJoinDecodeBHist
        (kernelNormalizationAuditJoinEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def kernelNormalizationAuditJoinDecodePacket
    (kernelStamp axiomQuery normalizationReplay closedNormal subjectBoundary nonescape routeJoin
      transport continuation provenance localName : RawEvent) :
    KernelNormalizationAuditJoinUp :=
  -- BEDC touchpoint anchor: BHist BMark
  KernelNormalizationAuditJoinUp.mk
    (kernelNormalizationAuditJoinDecodeBHist kernelStamp)
    (kernelNormalizationAuditJoinDecodeBHist axiomQuery)
    (kernelNormalizationAuditJoinDecodeBHist normalizationReplay)
    (kernelNormalizationAuditJoinDecodeBHist closedNormal)
    (kernelNormalizationAuditJoinDecodeBHist subjectBoundary)
    (kernelNormalizationAuditJoinDecodeBHist nonescape)
    (kernelNormalizationAuditJoinDecodeBHist routeJoin)
    (kernelNormalizationAuditJoinDecodeBHist transport)
    (kernelNormalizationAuditJoinDecodeBHist continuation)
    (kernelNormalizationAuditJoinDecodeBHist provenance)
    (kernelNormalizationAuditJoinDecodeBHist localName)

def kernelNormalizationAuditJoinToEventFlow :
    KernelNormalizationAuditJoinUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | KernelNormalizationAuditJoinUp.mk kernelStamp axiomQuery normalizationReplay closedNormal
      subjectBoundary nonescape routeJoin transport continuation provenance localName =>
      [kernelNormalizationAuditJoinEncodeBHist kernelStamp,
        kernelNormalizationAuditJoinEncodeBHist axiomQuery,
        kernelNormalizationAuditJoinEncodeBHist normalizationReplay,
        kernelNormalizationAuditJoinEncodeBHist closedNormal,
        kernelNormalizationAuditJoinEncodeBHist subjectBoundary,
        kernelNormalizationAuditJoinEncodeBHist nonescape,
        kernelNormalizationAuditJoinEncodeBHist routeJoin,
        kernelNormalizationAuditJoinEncodeBHist transport,
        kernelNormalizationAuditJoinEncodeBHist continuation,
        kernelNormalizationAuditJoinEncodeBHist provenance,
        kernelNormalizationAuditJoinEncodeBHist localName]

def kernelNormalizationAuditJoinFromEventFlow :
    EventFlow → Option KernelNormalizationAuditJoinUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | kernelStamp :: rest0 =>
      match rest0 with
      | [] => none
      | axiomQuery :: rest1 =>
          match rest1 with
          | [] => none
          | normalizationReplay :: rest2 =>
              match rest2 with
              | [] => none
              | closedNormal :: rest3 =>
                  match rest3 with
                  | [] => none
                  | subjectBoundary :: rest4 =>
                      match rest4 with
                      | [] => none
                      | nonescape :: rest5 =>
                          match rest5 with
                          | [] => none
                          | routeJoin :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | continuation :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | provenance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | localName :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (kernelNormalizationAuditJoinDecodePacket
                                                      kernelStamp axiomQuery
                                                      normalizationReplay closedNormal
                                                      subjectBoundary nonescape routeJoin
                                                      transport continuation provenance
                                                      localName)
                                              | _ :: _ => none

private theorem kernelNormalizationAuditJoin_round_trip :
    ∀ x : KernelNormalizationAuditJoinUp,
      kernelNormalizationAuditJoinFromEventFlow
        (kernelNormalizationAuditJoinToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk kernelStamp axiomQuery normalizationReplay closedNormal subjectBoundary nonescape
      routeJoin transport continuation provenance localName =>
      change
        some
            (kernelNormalizationAuditJoinDecodePacket
              (kernelNormalizationAuditJoinEncodeBHist kernelStamp)
              (kernelNormalizationAuditJoinEncodeBHist axiomQuery)
              (kernelNormalizationAuditJoinEncodeBHist normalizationReplay)
              (kernelNormalizationAuditJoinEncodeBHist closedNormal)
              (kernelNormalizationAuditJoinEncodeBHist subjectBoundary)
              (kernelNormalizationAuditJoinEncodeBHist nonescape)
              (kernelNormalizationAuditJoinEncodeBHist routeJoin)
              (kernelNormalizationAuditJoinEncodeBHist transport)
              (kernelNormalizationAuditJoinEncodeBHist continuation)
              (kernelNormalizationAuditJoinEncodeBHist provenance)
              (kernelNormalizationAuditJoinEncodeBHist localName)) =
          some
            (KernelNormalizationAuditJoinUp.mk kernelStamp axiomQuery normalizationReplay
              closedNormal subjectBoundary nonescape routeJoin transport continuation
              provenance localName)
      unfold kernelNormalizationAuditJoinDecodePacket
      rw [kernelNormalizationAuditJoinDecode_encode_bhist kernelStamp,
        kernelNormalizationAuditJoinDecode_encode_bhist axiomQuery,
        kernelNormalizationAuditJoinDecode_encode_bhist normalizationReplay,
        kernelNormalizationAuditJoinDecode_encode_bhist closedNormal,
        kernelNormalizationAuditJoinDecode_encode_bhist subjectBoundary,
        kernelNormalizationAuditJoinDecode_encode_bhist nonescape,
        kernelNormalizationAuditJoinDecode_encode_bhist routeJoin,
        kernelNormalizationAuditJoinDecode_encode_bhist transport,
        kernelNormalizationAuditJoinDecode_encode_bhist continuation,
        kernelNormalizationAuditJoinDecode_encode_bhist provenance,
        kernelNormalizationAuditJoinDecode_encode_bhist localName]

private theorem kernelNormalizationAuditJoinToEventFlow_injective
    {x y : KernelNormalizationAuditJoinUp} :
    kernelNormalizationAuditJoinToEventFlow x =
      kernelNormalizationAuditJoinToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kernelNormalizationAuditJoinFromEventFlow
          (kernelNormalizationAuditJoinToEventFlow x) =
        kernelNormalizationAuditJoinFromEventFlow
          (kernelNormalizationAuditJoinToEventFlow y) :=
    congrArg kernelNormalizationAuditJoinFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (kernelNormalizationAuditJoin_round_trip x).symm
      (Eq.trans hread (kernelNormalizationAuditJoin_round_trip y)))

def kernelNormalizationAuditJoinFields :
    KernelNormalizationAuditJoinUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KernelNormalizationAuditJoinUp.mk kernelStamp axiomQuery normalizationReplay closedNormal
      subjectBoundary nonescape routeJoin transport continuation provenance localName =>
      [kernelStamp, axiomQuery, normalizationReplay, closedNormal, subjectBoundary,
        nonescape, routeJoin, transport, continuation, provenance, localName]

private theorem kernelNormalizationAuditJoin_fields_faithful :
    ∀ x y : KernelNormalizationAuditJoinUp,
      kernelNormalizationAuditJoinFields x =
        kernelNormalizationAuditJoinFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  exact kernelNormalizationAuditJoinToEventFlow_injective (by
    cases x with
    | mk kernelStamp₁ axiomQuery₁ normalizationReplay₁ closedNormal₁ subjectBoundary₁
        nonescape₁ routeJoin₁ transport₁ continuation₁ provenance₁ localName₁ =>
        cases y with
        | mk kernelStamp₂ axiomQuery₂ normalizationReplay₂ closedNormal₂ subjectBoundary₂
            nonescape₂ routeJoin₂ transport₂ continuation₂ provenance₂ localName₂ =>
            injection hfields with hKernel tail0
            injection tail0 with hAxiom tail1
            injection tail1 with hReplay tail2
            injection tail2 with hClosed tail3
            injection tail3 with hSubject tail4
            injection tail4 with hNonescape tail5
            injection tail5 with hRoute tail6
            injection tail6 with hTransport tail7
            injection tail7 with hContinuation tail8
            injection tail8 with hProvenance tail9
            injection tail9 with hLocal _
            subst hKernel
            subst hAxiom
            subst hReplay
            subst hClosed
            subst hSubject
            subst hNonescape
            subst hRoute
            subst hTransport
            subst hContinuation
            subst hProvenance
            subst hLocal
            rfl)

instance kernelNormalizationAuditJoinBHistCarrier :
    BHistCarrier KernelNormalizationAuditJoinUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kernelNormalizationAuditJoinToEventFlow
  fromEventFlow := kernelNormalizationAuditJoinFromEventFlow

instance kernelNormalizationAuditJoinChapterTasteGate :
    ChapterTasteGate KernelNormalizationAuditJoinUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      kernelNormalizationAuditJoinFromEventFlow
        (kernelNormalizationAuditJoinToEventFlow x) = some x
    exact kernelNormalizationAuditJoin_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (kernelNormalizationAuditJoinToEventFlow_injective heq)

def taste_gate : ChapterTasteGate KernelNormalizationAuditJoinUp :=
  -- BEDC touchpoint anchor: BHist BMark
  kernelNormalizationAuditJoinChapterTasteGate

instance kernelNormalizationAuditJoinFieldFaithful :
    FieldFaithful KernelNormalizationAuditJoinUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := kernelNormalizationAuditJoinFields
  field_faithful := kernelNormalizationAuditJoin_fields_faithful

instance kernelNormalizationAuditJoinNontrivial :
    Nontrivial KernelNormalizationAuditJoinUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨KernelNormalizationAuditJoinUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      KernelNormalizationAuditJoinUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem KernelNormalizationAuditJoinTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      kernelNormalizationAuditJoinDecodeBHist
        (kernelNormalizationAuditJoinEncodeBHist h) = h) ∧
      (∀ x : KernelNormalizationAuditJoinUp,
        kernelNormalizationAuditJoinFromEventFlow
          (kernelNormalizationAuditJoinToEventFlow x) = some x) ∧
        (∀ x y : KernelNormalizationAuditJoinUp,
          kernelNormalizationAuditJoinToEventFlow x =
            kernelNormalizationAuditJoinToEventFlow y → x = y) ∧
          kernelNormalizationAuditJoinEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact kernelNormalizationAuditJoinDecode_encode_bhist
  · constructor
    · intro x
      change
        kernelNormalizationAuditJoinFromEventFlow
          (kernelNormalizationAuditJoinToEventFlow x) = some x
      exact kernelNormalizationAuditJoin_round_trip x
    · constructor
      · intro x y heq
        exact kernelNormalizationAuditJoinToEventFlow_injective heq
      · rfl

end BEDC.Derived.KernelNormalizationAuditJoinUp
