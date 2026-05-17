import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PackageMapBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PackageMapBoundaryUp : Type where
  | mk :
      (theoremMap gapMap traditionMap scientificMap axisBoundary auditRoute transport replay
        provenance nameCert : BHist) →
        PackageMapBoundaryUp
  deriving DecidableEq

def packageMapBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: packageMapBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: packageMapBoundaryEncodeBHist h

def packageMapBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (packageMapBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (packageMapBoundaryDecodeBHist tail)

private theorem PackageMapBoundaryTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, packageMapBoundaryDecodeBHist (packageMapBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def packageMapBoundaryFields : PackageMapBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PackageMapBoundaryUp.mk theoremMap gapMap traditionMap scientificMap axisBoundary auditRoute
      transport replay provenance nameCert =>
      [theoremMap, gapMap, traditionMap, scientificMap, axisBoundary, auditRoute, transport,
        replay, provenance, nameCert]

def packageMapBoundaryToEventFlow : PackageMapBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (packageMapBoundaryFields x).map packageMapBoundaryEncodeBHist

def packageMapBoundaryFromEventFlow : EventFlow → Option PackageMapBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | theoremMap :: rest0 =>
      match rest0 with
      | [] => none
      | gapMap :: rest1 =>
          match rest1 with
          | [] => none
          | traditionMap :: rest2 =>
              match rest2 with
              | [] => none
              | scientificMap :: rest3 =>
                  match rest3 with
                  | [] => none
                  | axisBoundary :: rest4 =>
                      match rest4 with
                      | [] => none
                      | auditRoute :: rest5 =>
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
                                      | nameCert :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (PackageMapBoundaryUp.mk
                                                  (packageMapBoundaryDecodeBHist theoremMap)
                                                  (packageMapBoundaryDecodeBHist gapMap)
                                                  (packageMapBoundaryDecodeBHist traditionMap)
                                                  (packageMapBoundaryDecodeBHist scientificMap)
                                                  (packageMapBoundaryDecodeBHist axisBoundary)
                                                  (packageMapBoundaryDecodeBHist auditRoute)
                                                  (packageMapBoundaryDecodeBHist transport)
                                                  (packageMapBoundaryDecodeBHist replay)
                                                  (packageMapBoundaryDecodeBHist provenance)
                                                  (packageMapBoundaryDecodeBHist nameCert))
                                          | _ :: _ => none

private theorem PackageMapBoundaryTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PackageMapBoundaryUp,
      packageMapBoundaryFromEventFlow (packageMapBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk theoremMap gapMap traditionMap scientificMap axisBoundary auditRoute transport replay
      provenance nameCert =>
      change
        some
          (PackageMapBoundaryUp.mk
            (packageMapBoundaryDecodeBHist (packageMapBoundaryEncodeBHist theoremMap))
            (packageMapBoundaryDecodeBHist (packageMapBoundaryEncodeBHist gapMap))
            (packageMapBoundaryDecodeBHist (packageMapBoundaryEncodeBHist traditionMap))
            (packageMapBoundaryDecodeBHist (packageMapBoundaryEncodeBHist scientificMap))
            (packageMapBoundaryDecodeBHist (packageMapBoundaryEncodeBHist axisBoundary))
            (packageMapBoundaryDecodeBHist (packageMapBoundaryEncodeBHist auditRoute))
            (packageMapBoundaryDecodeBHist (packageMapBoundaryEncodeBHist transport))
            (packageMapBoundaryDecodeBHist (packageMapBoundaryEncodeBHist replay))
            (packageMapBoundaryDecodeBHist (packageMapBoundaryEncodeBHist provenance))
            (packageMapBoundaryDecodeBHist (packageMapBoundaryEncodeBHist nameCert))) =
          some
            (PackageMapBoundaryUp.mk theoremMap gapMap traditionMap scientificMap axisBoundary
              auditRoute transport replay provenance nameCert)
      rw [PackageMapBoundaryTasteGate_single_carrier_alignment_decode_encode theoremMap,
        PackageMapBoundaryTasteGate_single_carrier_alignment_decode_encode gapMap,
        PackageMapBoundaryTasteGate_single_carrier_alignment_decode_encode traditionMap,
        PackageMapBoundaryTasteGate_single_carrier_alignment_decode_encode scientificMap,
        PackageMapBoundaryTasteGate_single_carrier_alignment_decode_encode axisBoundary,
        PackageMapBoundaryTasteGate_single_carrier_alignment_decode_encode auditRoute,
        PackageMapBoundaryTasteGate_single_carrier_alignment_decode_encode transport,
        PackageMapBoundaryTasteGate_single_carrier_alignment_decode_encode replay,
        PackageMapBoundaryTasteGate_single_carrier_alignment_decode_encode provenance,
        PackageMapBoundaryTasteGate_single_carrier_alignment_decode_encode nameCert]

private theorem PackageMapBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PackageMapBoundaryUp} :
    packageMapBoundaryToEventFlow x = packageMapBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      packageMapBoundaryFromEventFlow (packageMapBoundaryToEventFlow x) =
        packageMapBoundaryFromEventFlow (packageMapBoundaryToEventFlow y) :=
    congrArg packageMapBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PackageMapBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PackageMapBoundaryTasteGate_single_carrier_alignment_round_trip y)))

private theorem PackageMapBoundaryTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : PackageMapBoundaryUp,
      packageMapBoundaryFields x = packageMapBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk theoremMap₁ gapMap₁ traditionMap₁ scientificMap₁ axisBoundary₁ auditRoute₁
      transport₁ replay₁ provenance₁ nameCert₁ =>
      cases y with
      | mk theoremMap₂ gapMap₂ traditionMap₂ scientificMap₂ axisBoundary₂ auditRoute₂
          transport₂ replay₂ provenance₂ nameCert₂ =>
          injection hfields with hTheoremMap tail0
          injection tail0 with hGapMap tail1
          injection tail1 with hTraditionMap tail2
          injection tail2 with hScientificMap tail3
          injection tail3 with hAxisBoundary tail4
          injection tail4 with hAuditRoute tail5
          injection tail5 with hTransport tail6
          injection tail6 with hReplay tail7
          injection tail7 with hProvenance tail8
          injection tail8 with hNameCert _
          subst hTheoremMap
          subst hGapMap
          subst hTraditionMap
          subst hScientificMap
          subst hAxisBoundary
          subst hAuditRoute
          subst hTransport
          subst hReplay
          subst hProvenance
          subst hNameCert
          rfl

instance packageMapBoundaryBHistCarrier : BHistCarrier PackageMapBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := packageMapBoundaryToEventFlow
  fromEventFlow := packageMapBoundaryFromEventFlow

instance packageMapBoundaryChapterTasteGate : ChapterTasteGate PackageMapBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change packageMapBoundaryFromEventFlow (packageMapBoundaryToEventFlow x) = some x
    exact PackageMapBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PackageMapBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance packageMapBoundaryFieldFaithful : FieldFaithful PackageMapBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := packageMapBoundaryFields
  field_faithful := PackageMapBoundaryTasteGate_single_carrier_alignment_fields_faithful

instance packageMapBoundaryNontrivial : Nontrivial PackageMapBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PackageMapBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PackageMapBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PackageMapBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  packageMapBoundaryChapterTasteGate

theorem PackageMapBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist, packageMapBoundaryDecodeBHist (packageMapBoundaryEncodeBHist h) = h) ∧
      (∀ x : PackageMapBoundaryUp,
        packageMapBoundaryFromEventFlow (packageMapBoundaryToEventFlow x) = some x) ∧
        (∀ x y : PackageMapBoundaryUp,
          packageMapBoundaryToEventFlow x = packageMapBoundaryToEventFlow y → x = y) ∧
          packageMapBoundaryFields
              (PackageMapBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
            [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
              BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] ∧
            packageMapBoundaryEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
              Nonempty (ChapterTasteGate PackageMapBoundaryUp) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨PackageMapBoundaryTasteGate_single_carrier_alignment_decode_encode,
      PackageMapBoundaryTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => PackageMapBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl,
      rfl,
      ⟨packageMapBoundaryChapterTasteGate⟩⟩

end BEDC.Derived.PackageMapBoundaryUp
