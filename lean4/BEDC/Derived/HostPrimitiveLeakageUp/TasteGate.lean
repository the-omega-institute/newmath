import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HostPrimitiveLeakageUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HostPrimitiveLeakageUp : Type where
  | mk :
      (site request replacement diagnostic failedGate auditBoundary transport replay provenance
        nameRow : BHist) →
      HostPrimitiveLeakageUp
  deriving DecidableEq

def hostPrimitiveLeakageEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hostPrimitiveLeakageEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hostPrimitiveLeakageEncodeBHist h

def hostPrimitiveLeakageDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hostPrimitiveLeakageDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hostPrimitiveLeakageDecodeBHist tail)

private theorem hostPrimitiveLeakageDecode_encode_bhist :
    ∀ h : BHist, hostPrimitiveLeakageDecodeBHist (hostPrimitiveLeakageEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hostPrimitiveLeakageToEventFlow : HostPrimitiveLeakageUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HostPrimitiveLeakageUp.mk site request replacement diagnostic failedGate auditBoundary
      transport replay provenance nameRow =>
      [hostPrimitiveLeakageEncodeBHist site,
        hostPrimitiveLeakageEncodeBHist request,
        hostPrimitiveLeakageEncodeBHist replacement,
        hostPrimitiveLeakageEncodeBHist diagnostic,
        hostPrimitiveLeakageEncodeBHist failedGate,
        hostPrimitiveLeakageEncodeBHist auditBoundary,
        hostPrimitiveLeakageEncodeBHist transport,
        hostPrimitiveLeakageEncodeBHist replay,
        hostPrimitiveLeakageEncodeBHist provenance,
        hostPrimitiveLeakageEncodeBHist nameRow]

def hostPrimitiveLeakageFromEventFlow : EventFlow → Option HostPrimitiveLeakageUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | site :: rest0 =>
      match rest0 with
      | [] => none
      | request :: rest1 =>
          match rest1 with
          | [] => none
          | replacement :: rest2 =>
              match rest2 with
              | [] => none
              | diagnostic :: rest3 =>
                  match rest3 with
                  | [] => none
                  | failedGate :: rest4 =>
                      match rest4 with
                      | [] => none
                      | auditBoundary :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | replay :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | nameRow :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (HostPrimitiveLeakageUp.mk
                                                  (hostPrimitiveLeakageDecodeBHist site)
                                                  (hostPrimitiveLeakageDecodeBHist request)
                                                  (hostPrimitiveLeakageDecodeBHist replacement)
                                                  (hostPrimitiveLeakageDecodeBHist diagnostic)
                                                  (hostPrimitiveLeakageDecodeBHist failedGate)
                                                  (hostPrimitiveLeakageDecodeBHist auditBoundary)
                                                  (hostPrimitiveLeakageDecodeBHist transport)
                                                  (hostPrimitiveLeakageDecodeBHist replay)
                                                  (hostPrimitiveLeakageDecodeBHist provenance)
                                                  (hostPrimitiveLeakageDecodeBHist nameRow))
                                          | _ :: _ => none

private theorem hostPrimitiveLeakage_round_trip :
    ∀ x : HostPrimitiveLeakageUp,
      hostPrimitiveLeakageFromEventFlow (hostPrimitiveLeakageToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk site request replacement diagnostic failedGate auditBoundary transport replay provenance
      nameRow =>
      change
        some
          (HostPrimitiveLeakageUp.mk
            (hostPrimitiveLeakageDecodeBHist (hostPrimitiveLeakageEncodeBHist site))
            (hostPrimitiveLeakageDecodeBHist (hostPrimitiveLeakageEncodeBHist request))
            (hostPrimitiveLeakageDecodeBHist (hostPrimitiveLeakageEncodeBHist replacement))
            (hostPrimitiveLeakageDecodeBHist (hostPrimitiveLeakageEncodeBHist diagnostic))
            (hostPrimitiveLeakageDecodeBHist (hostPrimitiveLeakageEncodeBHist failedGate))
            (hostPrimitiveLeakageDecodeBHist (hostPrimitiveLeakageEncodeBHist auditBoundary))
            (hostPrimitiveLeakageDecodeBHist (hostPrimitiveLeakageEncodeBHist transport))
            (hostPrimitiveLeakageDecodeBHist (hostPrimitiveLeakageEncodeBHist replay))
            (hostPrimitiveLeakageDecodeBHist (hostPrimitiveLeakageEncodeBHist provenance))
            (hostPrimitiveLeakageDecodeBHist (hostPrimitiveLeakageEncodeBHist nameRow))) =
          some
            (HostPrimitiveLeakageUp.mk site request replacement diagnostic failedGate
              auditBoundary transport replay provenance nameRow)
      rw [hostPrimitiveLeakageDecode_encode_bhist site,
        hostPrimitiveLeakageDecode_encode_bhist request,
        hostPrimitiveLeakageDecode_encode_bhist replacement,
        hostPrimitiveLeakageDecode_encode_bhist diagnostic,
        hostPrimitiveLeakageDecode_encode_bhist failedGate,
        hostPrimitiveLeakageDecode_encode_bhist auditBoundary,
        hostPrimitiveLeakageDecode_encode_bhist transport,
        hostPrimitiveLeakageDecode_encode_bhist replay,
        hostPrimitiveLeakageDecode_encode_bhist provenance,
        hostPrimitiveLeakageDecode_encode_bhist nameRow]

private theorem hostPrimitiveLeakageToEventFlow_injective {x y : HostPrimitiveLeakageUp} :
    hostPrimitiveLeakageToEventFlow x = hostPrimitiveLeakageToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hostPrimitiveLeakageFromEventFlow (hostPrimitiveLeakageToEventFlow x) =
        hostPrimitiveLeakageFromEventFlow (hostPrimitiveLeakageToEventFlow y) :=
    congrArg hostPrimitiveLeakageFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hostPrimitiveLeakage_round_trip x).symm
      (Eq.trans hread (hostPrimitiveLeakage_round_trip y)))

instance hostPrimitiveLeakageBHistCarrier : BHistCarrier HostPrimitiveLeakageUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hostPrimitiveLeakageToEventFlow
  fromEventFlow := hostPrimitiveLeakageFromEventFlow

instance hostPrimitiveLeakageChapterTasteGate : ChapterTasteGate HostPrimitiveLeakageUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hostPrimitiveLeakageFromEventFlow (hostPrimitiveLeakageToEventFlow x) = some x
    exact hostPrimitiveLeakage_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hostPrimitiveLeakageToEventFlow_injective heq)

instance hostPrimitiveLeakageFieldFaithful : FieldFaithful HostPrimitiveLeakageUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | HostPrimitiveLeakageUp.mk site request replacement diagnostic failedGate auditBoundary
        transport replay provenance nameRow =>
        [site, request, replacement, diagnostic, failedGate, auditBoundary, transport, replay,
          provenance, nameRow]
  field_faithful := by
    intro x y h
    cases x with
    | mk site₁ request₁ replacement₁ diagnostic₁ failedGate₁ auditBoundary₁ transport₁ replay₁
        provenance₁ nameRow₁ =>
        cases y with
        | mk site₂ request₂ replacement₂ diagnostic₂ failedGate₂ auditBoundary₂ transport₂ replay₂
            provenance₂ nameRow₂ =>
            injection h with hSite hRest₁
            injection hRest₁ with hRequest hRest₂
            injection hRest₂ with hReplacement hRest₃
            injection hRest₃ with hDiagnostic hRest₄
            injection hRest₄ with hFailedGate hRest₅
            injection hRest₅ with hAuditBoundary hRest₆
            injection hRest₆ with hTransport hRest₇
            injection hRest₇ with hReplay hRest₈
            injection hRest₈ with hProvenance hRest₉
            injection hRest₉ with hNameRow _
            cases hSite
            cases hRequest
            cases hReplacement
            cases hDiagnostic
            cases hFailedGate
            cases hAuditBoundary
            cases hTransport
            cases hReplay
            cases hProvenance
            cases hNameRow
            rfl

instance hostPrimitiveLeakageNontrivial : Nontrivial HostPrimitiveLeakageUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HostPrimitiveLeakageUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HostPrimitiveLeakageUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HostPrimitiveLeakageUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hostPrimitiveLeakageChapterTasteGate

theorem HostPrimitiveLeakageTasteGate_single_carrier_alignment :
    (∀ h : BHist, hostPrimitiveLeakageDecodeBHist (hostPrimitiveLeakageEncodeBHist h) = h) ∧
      (∀ x : HostPrimitiveLeakageUp,
        hostPrimitiveLeakageFromEventFlow (hostPrimitiveLeakageToEventFlow x) = some x) ∧
        (∀ x y : HostPrimitiveLeakageUp,
          hostPrimitiveLeakageToEventFlow x = hostPrimitiveLeakageToEventFlow y → x = y) ∧
          hostPrimitiveLeakageEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact hostPrimitiveLeakageDecode_encode_bhist
  · constructor
    · exact hostPrimitiveLeakage_round_trip
    · constructor
      · intro x y heq
        exact hostPrimitiveLeakageToEventFlow_injective heq
      · rfl

end BEDC.Derived.HostPrimitiveLeakageUp
