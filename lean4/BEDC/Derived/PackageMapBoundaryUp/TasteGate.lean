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
        provenance localName : BHist) →
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

private theorem packageMapBoundaryDecode_encode_bhist :
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

private theorem packageMapBoundary_mk_congr
    {theoremMap theoremMap' gapMap gapMap' traditionMap traditionMap'
      scientificMap scientificMap' axisBoundary axisBoundary' auditRoute auditRoute'
      transport transport' replay replay' provenance provenance' localName localName' : BHist}
    (hTheoremMap : theoremMap' = theoremMap)
    (hGapMap : gapMap' = gapMap)
    (hTraditionMap : traditionMap' = traditionMap)
    (hScientificMap : scientificMap' = scientificMap)
    (hAxisBoundary : axisBoundary' = axisBoundary)
    (hAuditRoute : auditRoute' = auditRoute)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    PackageMapBoundaryUp.mk theoremMap' gapMap' traditionMap' scientificMap' axisBoundary'
        auditRoute' transport' replay' provenance' localName' =
      PackageMapBoundaryUp.mk theoremMap gapMap traditionMap scientificMap axisBoundary
        auditRoute transport replay provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hTheoremMap
  cases hGapMap
  cases hTraditionMap
  cases hScientificMap
  cases hAxisBoundary
  cases hAuditRoute
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hLocalName
  rfl

def packageMapBoundaryFields : PackageMapBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PackageMapBoundaryUp.mk theoremMap gapMap traditionMap scientificMap axisBoundary
      auditRoute transport replay provenance localName =>
      [theoremMap, gapMap, traditionMap, scientificMap, axisBoundary, auditRoute, transport,
        replay, provenance, localName]

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
                                      | localName :: rest9 =>
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
                                                  (packageMapBoundaryDecodeBHist localName))
                                          | _ :: _ => none

private theorem packageMapBoundary_round_trip :
    ∀ x : PackageMapBoundaryUp,
      packageMapBoundaryFromEventFlow (packageMapBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk theoremMap gapMap traditionMap scientificMap axisBoundary auditRoute transport replay
      provenance localName =>
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
            (packageMapBoundaryDecodeBHist (packageMapBoundaryEncodeBHist localName))) =
          some
            (PackageMapBoundaryUp.mk theoremMap gapMap traditionMap scientificMap axisBoundary
              auditRoute transport replay provenance localName)
      exact
        congrArg some
          (packageMapBoundary_mk_congr
            (packageMapBoundaryDecode_encode_bhist theoremMap)
            (packageMapBoundaryDecode_encode_bhist gapMap)
            (packageMapBoundaryDecode_encode_bhist traditionMap)
            (packageMapBoundaryDecode_encode_bhist scientificMap)
            (packageMapBoundaryDecode_encode_bhist axisBoundary)
            (packageMapBoundaryDecode_encode_bhist auditRoute)
            (packageMapBoundaryDecode_encode_bhist transport)
            (packageMapBoundaryDecode_encode_bhist replay)
            (packageMapBoundaryDecode_encode_bhist provenance)
            (packageMapBoundaryDecode_encode_bhist localName))

private theorem packageMapBoundaryToEventFlow_injective {x y : PackageMapBoundaryUp} :
    packageMapBoundaryToEventFlow x = packageMapBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      packageMapBoundaryFromEventFlow (packageMapBoundaryToEventFlow x) =
        packageMapBoundaryFromEventFlow (packageMapBoundaryToEventFlow y) :=
    congrArg packageMapBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (packageMapBoundary_round_trip x).symm
      (Eq.trans hread (packageMapBoundary_round_trip y)))

private theorem packageMapBoundary_fields_faithful :
    ∀ x y : PackageMapBoundaryUp,
      packageMapBoundaryFields x = packageMapBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk theoremMap₁ gapMap₁ traditionMap₁ scientificMap₁ axisBoundary₁ auditRoute₁
      transport₁ replay₁ provenance₁ localName₁ =>
      cases y with
      | mk theoremMap₂ gapMap₂ traditionMap₂ scientificMap₂ axisBoundary₂ auditRoute₂
          transport₂ replay₂ provenance₂ localName₂ =>
          injection hfields with hTheoremMap tail0
          injection tail0 with hGapMap tail1
          injection tail1 with hTraditionMap tail2
          injection tail2 with hScientificMap tail3
          injection tail3 with hAxisBoundary tail4
          injection tail4 with hAuditRoute tail5
          injection tail5 with hTransport tail6
          injection tail6 with hReplay tail7
          injection tail7 with hProvenance tail8
          injection tail8 with hLocalName _
          subst hTheoremMap
          subst hGapMap
          subst hTraditionMap
          subst hScientificMap
          subst hAxisBoundary
          subst hAuditRoute
          subst hTransport
          subst hReplay
          subst hProvenance
          subst hLocalName
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
    exact packageMapBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (packageMapBoundaryToEventFlow_injective heq)

instance packageMapBoundaryFieldFaithful : FieldFaithful PackageMapBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := packageMapBoundaryFields
  field_faithful := packageMapBoundary_fields_faithful

instance packageMapBoundaryNontrivial : Nontrivial PackageMapBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PackageMapBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PackageMapBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PackageMapBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  packageMapBoundaryChapterTasteGate

theorem PackageMapBoundaryUp_single_carrier_alignment :
    (∀ h : BHist, packageMapBoundaryDecodeBHist (packageMapBoundaryEncodeBHist h) = h) ∧
      (∀ x : PackageMapBoundaryUp,
        packageMapBoundaryFromEventFlow (packageMapBoundaryToEventFlow x) = some x) ∧
        (∀ x y : PackageMapBoundaryUp,
          packageMapBoundaryToEventFlow x = packageMapBoundaryToEventFlow y → x = y) ∧
          packageMapBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨packageMapBoundaryDecode_encode_bhist, packageMapBoundary_round_trip,
      (fun _ _ heq => packageMapBoundaryToEventFlow_injective heq), rfl⟩

end BEDC.Derived.PackageMapBoundaryUp
