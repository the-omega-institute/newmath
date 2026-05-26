import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

/-!
# DyadicIntervalBasisUp TasteGate carrier.
-/

namespace BEDC.Derived.DyadicIntervalBasisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Finite dyadic interval basis token with the nine BEDC rows visible to consumers. -/
inductive DyadicIntervalBasisUp : Type where
  | mk :
      (cell endpointLedger containment readback basisRead transport replay provenance nameCert :
        BHist) →
      DyadicIntervalBasisUp
  deriving DecidableEq

def dyadicIntervalBasisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicIntervalBasisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicIntervalBasisEncodeBHist h

def dyadicIntervalBasisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicIntervalBasisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicIntervalBasisDecodeBHist tail)

private theorem DyadicIntervalBasisTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      dyadicIntervalBasisDecodeBHist (dyadicIntervalBasisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def dyadicIntervalBasisFields : DyadicIntervalBasisUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicIntervalBasisUp.mk cell endpointLedger containment readback basisRead transport replay
      provenance nameCert =>
      [cell, endpointLedger, containment, readback, basisRead, transport, replay, provenance,
        nameCert]

def dyadicIntervalBasisToEventFlow : DyadicIntervalBasisUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicIntervalBasisFields x).map dyadicIntervalBasisEncodeBHist

def dyadicIntervalBasisFromEventFlow : EventFlow → Option DyadicIntervalBasisUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | cell :: rest0 =>
      match rest0 with
      | [] => none
      | endpointLedger :: rest1 =>
          match rest1 with
          | [] => none
          | containment :: rest2 =>
              match rest2 with
              | [] => none
              | readback :: rest3 =>
                  match rest3 with
                  | [] => none
                  | basisRead :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | replay :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | nameCert :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (DyadicIntervalBasisUp.mk
                                              (dyadicIntervalBasisDecodeBHist cell)
                                              (dyadicIntervalBasisDecodeBHist endpointLedger)
                                              (dyadicIntervalBasisDecodeBHist containment)
                                              (dyadicIntervalBasisDecodeBHist readback)
                                              (dyadicIntervalBasisDecodeBHist basisRead)
                                              (dyadicIntervalBasisDecodeBHist transport)
                                              (dyadicIntervalBasisDecodeBHist replay)
                                              (dyadicIntervalBasisDecodeBHist provenance)
                                              (dyadicIntervalBasisDecodeBHist nameCert))
                                      | _ :: _ => none

private theorem DyadicIntervalBasisTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DyadicIntervalBasisUp,
      dyadicIntervalBasisFromEventFlow (dyadicIntervalBasisToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk cell endpointLedger containment readback basisRead transport replay provenance nameCert =>
      change
        some
          (DyadicIntervalBasisUp.mk
            (dyadicIntervalBasisDecodeBHist (dyadicIntervalBasisEncodeBHist cell))
            (dyadicIntervalBasisDecodeBHist (dyadicIntervalBasisEncodeBHist endpointLedger))
            (dyadicIntervalBasisDecodeBHist (dyadicIntervalBasisEncodeBHist containment))
            (dyadicIntervalBasisDecodeBHist (dyadicIntervalBasisEncodeBHist readback))
            (dyadicIntervalBasisDecodeBHist (dyadicIntervalBasisEncodeBHist basisRead))
            (dyadicIntervalBasisDecodeBHist (dyadicIntervalBasisEncodeBHist transport))
            (dyadicIntervalBasisDecodeBHist (dyadicIntervalBasisEncodeBHist replay))
            (dyadicIntervalBasisDecodeBHist (dyadicIntervalBasisEncodeBHist provenance))
            (dyadicIntervalBasisDecodeBHist (dyadicIntervalBasisEncodeBHist nameCert))) =
          some
            (DyadicIntervalBasisUp.mk cell endpointLedger containment readback basisRead
              transport replay provenance nameCert)
      rw [DyadicIntervalBasisTasteGate_single_carrier_alignment_decode_encode cell,
        DyadicIntervalBasisTasteGate_single_carrier_alignment_decode_encode endpointLedger,
        DyadicIntervalBasisTasteGate_single_carrier_alignment_decode_encode containment,
        DyadicIntervalBasisTasteGate_single_carrier_alignment_decode_encode readback,
        DyadicIntervalBasisTasteGate_single_carrier_alignment_decode_encode basisRead,
        DyadicIntervalBasisTasteGate_single_carrier_alignment_decode_encode transport,
        DyadicIntervalBasisTasteGate_single_carrier_alignment_decode_encode replay,
        DyadicIntervalBasisTasteGate_single_carrier_alignment_decode_encode provenance,
        DyadicIntervalBasisTasteGate_single_carrier_alignment_decode_encode nameCert]

private theorem DyadicIntervalBasisTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicIntervalBasisUp} :
    dyadicIntervalBasisToEventFlow x = dyadicIntervalBasisToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicIntervalBasisFromEventFlow (dyadicIntervalBasisToEventFlow x) =
        dyadicIntervalBasisFromEventFlow (dyadicIntervalBasisToEventFlow y) :=
    congrArg dyadicIntervalBasisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DyadicIntervalBasisTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DyadicIntervalBasisTasteGate_single_carrier_alignment_round_trip y)))

private theorem DyadicIntervalBasisTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : DyadicIntervalBasisUp, dyadicIntervalBasisFields x = dyadicIntervalBasisFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk cell₁ endpointLedger₁ containment₁ readback₁ basisRead₁ transport₁ replay₁
      provenance₁ nameCert₁ =>
      cases y with
      | mk cell₂ endpointLedger₂ containment₂ readback₂ basisRead₂ transport₂ replay₂
          provenance₂ nameCert₂ =>
          injection hfields with hCell tail0
          injection tail0 with hEndpointLedger tail1
          injection tail1 with hContainment tail2
          injection tail2 with hReadback tail3
          injection tail3 with hBasisRead tail4
          injection tail4 with hTransport tail5
          injection tail5 with hReplay tail6
          injection tail6 with hProvenance tail7
          injection tail7 with hNameCert _
          subst hCell
          subst hEndpointLedger
          subst hContainment
          subst hReadback
          subst hBasisRead
          subst hTransport
          subst hReplay
          subst hProvenance
          subst hNameCert
          rfl

instance dyadicIntervalBasisBHistCarrier : BHistCarrier DyadicIntervalBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicIntervalBasisToEventFlow
  fromEventFlow := dyadicIntervalBasisFromEventFlow

instance dyadicIntervalBasisChapterTasteGate : ChapterTasteGate DyadicIntervalBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicIntervalBasisFromEventFlow (dyadicIntervalBasisToEventFlow x) = some x
    exact DyadicIntervalBasisTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicIntervalBasisTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance dyadicIntervalBasisFieldFaithful : FieldFaithful DyadicIntervalBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicIntervalBasisFields
  field_faithful := DyadicIntervalBasisTasteGate_single_carrier_alignment_fields_faithful

def taste_gate : ChapterTasteGate DyadicIntervalBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicIntervalBasisChapterTasteGate

theorem DyadicIntervalBasisTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicIntervalBasisDecodeBHist (dyadicIntervalBasisEncodeBHist h) = h) ∧
      (∀ x : DyadicIntervalBasisUp,
        dyadicIntervalBasisFromEventFlow (dyadicIntervalBasisToEventFlow x) = some x) ∧
        (∀ x y : DyadicIntervalBasisUp,
          dyadicIntervalBasisToEventFlow x = dyadicIntervalBasisToEventFlow y → x = y) ∧
          dyadicIntervalBasisEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨DyadicIntervalBasisTasteGate_single_carrier_alignment_decode_encode,
      DyadicIntervalBasisTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        DyadicIntervalBasisTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DyadicIntervalBasisUp
