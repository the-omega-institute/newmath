import BEDC.Derived.CommRingUp
import BEDC.Derived.RingedSpaceUp
import BEDC.Derived.SheafUp
import BEDC.Derived.TopologyUp.Singleton

namespace BEDC.Derived.SchemeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.CommRingUp
open BEDC.Derived.RingedSpaceUp
open BEDC.Derived.SheafUp
open BEDC.Derived.TopologyUp

theorem SchemeAffineCoverRow_semantic_name_certificate
    {point openHist sectionHist germ ringEndpoint chartEndpoint : BHist}
    (package : RingedSpaceSingletonPackage point openHist sectionHist germ ringEndpoint)
    (chart : CommRingSingletonClassifier chartEndpoint BHist.Empty) :
    SemanticNameCert
      (fun endpoint : BHist =>
        RingedSpaceSingletonPackage point openHist sectionHist germ endpoint ∧
          CommRingSingletonClassifier chartEndpoint BHist.Empty)
      (fun endpoint : BHist =>
        RingedSpaceSingletonPackage point openHist sectionHist germ endpoint ∧
          CommRingSingletonClassifier chartEndpoint BHist.Empty)
      (fun endpoint : BHist =>
        RingedSpaceSingletonPackage point openHist sectionHist germ endpoint ∧
          CommRingSingletonClassifier chartEndpoint BHist.Empty)
      hsame := by
  constructor
  · constructor
    · exact Exists.intro ringEndpoint (And.intro package chart)
    · intro endpoint _carrier
      exact hsame_refl endpoint
    · intro endpoint endpoint' same
      exact hsame_symm same
    · intro endpoint endpoint' endpoint'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro endpoint endpoint' same carrier
      cases same
      exact carrier
  · intro _endpoint source
    exact source
  · intro _endpoint source
    exact source

theorem SchemeAffineChartLedger_overlap_locality_obligation
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB chartA chartB ringEndpointA ringEndpointB : BHist} :
    RingedSpaceSingletonPackage point openHist sectionA germA ringEndpointA ->
      RingedSpaceSingletonPackage point openHist sectionB germB ringEndpointB ->
        CommRingSingletonClassifier chartA ringEndpointA ->
          CommRingSingletonClassifier chartB ringEndpointB ->
            hsame germA germB ->
              hsame openHist restrictedOpen ->
                Cont restrictedOpen sectionA restrictedGermA ->
                  Cont restrictedOpen sectionB restrictedGermB ->
                    SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
                      SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
                        hsame restrictedGermA restrictedGermB ∧
                          CommRingSingletonClassifier chartA chartB := by
  intro packageA packageB chartClassA chartClassB sameGerm sameOpen restrictedA restrictedB
  have descent :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          hsame restrictedGermA restrictedGermB :=
    SheafRestrictedOpenCarrier_locality_gluing_descent
      packageA.left packageB.left sameGerm sameOpen restrictedA restrictedB
  have sameChart : hsame chartA chartB :=
    hsame_trans chartClassA.left (hsame_symm chartClassB.left)
  have chartClassifier : CommRingSingletonClassifier chartA chartB :=
    And.intro chartClassA.left
      (And.intro chartClassB.left sameChart)
  exact And.intro descent.left
    (And.intro descent.right.left (And.intro descent.right.right chartClassifier))

theorem SchemeSingleton_affine_cover_ledger_exactness
    {point openHist sectionHist germ ringEndpoint chartEndpoint restrictedOpen
      restrictedGerm : BHist} :
    RingedSpaceSingletonSurface point openHist sectionHist germ ringEndpoint ->
      CommRingSingletonClassifier chartEndpoint BHist.Empty ->
        hsame openHist restrictedOpen -> Cont restrictedOpen sectionHist restrictedGerm ->
          RingedSpaceSingletonSurface point restrictedOpen sectionHist restrictedGerm
              chartEndpoint ∧
            CommRingSingletonClassifier chartEndpoint BHist.Empty ∧ hsame germ restrictedGerm := by
  intro surface chartClass sameOpen restrictedRow
  have readback :=
    SheafBHistPointGermLedger_restriction_readback surface.right.left sameOpen restrictedRow
  have restrictedOpenAt : TopologySingletonOpenAt restrictedOpen point :=
    And.intro (hsame_trans (hsame_symm sameOpen) surface.left.left) surface.left.right
  exact And.intro
    (And.intro restrictedOpenAt (And.intro readback.left chartClass))
    (And.intro chartClass readback.right)

theorem SchemeSingleton_affine_cover_nerve_empty_boundary
    {point ambient member overlap route germ operationA operationB operationC : BHist} :
    TopologySingletonOpenAt BHist.Empty point ->
      SheafBHistCoverNerveLedger ambient member overlap route germ ->
        hsame germ BHist.Empty ->
          CommRingSingletonClassifier operationA operationB ->
            CommRingSingletonClassifier operationB operationC ->
              hsame overlap BHist.Empty ∧ hsame route BHist.Empty ∧
                CommRingSingletonClassifier operationA operationC ∧
                  TopologySingletonOpenAt BHist.Empty point := by
  intro openPoint ledger germEmpty commAB commBC
  have ringedBoundary :=
    RingedSpaceSingleton_cover_nerve_empty_boundary openPoint ledger germEmpty commAB
  have commAC : CommRingSingletonClassifier operationA operationC :=
    And.intro commAB.left
      (And.intro commBC.right.left
        (hsame_trans commAB.right.right commBC.right.right))
  exact And.intro ringedBoundary.left
    (And.intro ringedBoundary.right.left
      (And.intro commAC ringedBoundary.right.right.right))

def SchemeSingletonPackage
    (point openHist sectionHist germ ringEndpoint chartA chartB overlap : BHist) : Prop :=
  RingedSpaceSingletonSurface point openHist sectionHist germ ringEndpoint ∧
    CommRingSingletonClassifier chartA BHist.Empty ∧
      CommRingSingletonClassifier chartB BHist.Empty ∧
        SheafBHistPointGermComparison point openHist sectionHist germ openHist sectionHist germ
          overlap

theorem SchemeSingletonPackage_carrier_source_obligation
    {point openHist sectionHist germ ringEndpoint chartA chartB overlap tail : BHist} :
    SchemeSingletonPackage point openHist sectionHist germ ringEndpoint chartA chartB overlap ->
      RingedSpaceSingletonSurface point openHist sectionHist germ ringEndpoint ∧
        CommRingSingletonCarrier chartA ∧ CommRingSingletonCarrier chartB ∧
          SheafBHistPointGermComparison point openHist sectionHist germ openHist sectionHist germ
            overlap ∧
            (hsame overlap (BHist.e0 tail) -> False) := by
  intro package
  have overlapNotZero : hsame overlap (BHist.e0 tail) -> False := by
    intro sameZero
    exact unary_no_zero_extension
      (unary_transport package.right.right.right.right.right.right.left sameZero)
  exact And.intro package.left
    (And.intro package.right.left.left
      (And.intro package.right.right.left.left
        (And.intro package.right.right.right overlapNotZero)))

theorem SchemeAffineCoverClassifier_overlap_locality
    {point openA openB sectionA sectionB germA germB ringA ringB chartA chartB common : BHist} :
    RingedSpaceSingletonSurface point openA sectionA germA ringA ->
      RingedSpaceSingletonSurface point openB sectionB germB ringB ->
        SheafBHistPointGermComparison point openA sectionA germA openB sectionB germB common ->
          CommRingSingletonClassifier chartA ringA ->
            CommRingSingletonClassifier chartB ringB ->
              hsame germA germB ∧ CommRingSingletonCarrier ringA ∧
                CommRingSingletonCarrier ringB := by
  intro _surfaceA _surfaceB comparison chartAClassified chartBClassified
  exact And.intro comparison.right.right.right.right.right.right.right.right
    (And.intro chartAClassified.right.left chartBClassified.right.left)

theorem SchemeSingleton_affine_cover_classifier_locality_obligation
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB ringEndpoint chartA chartB : BHist} :
    RingedSpaceSingletonSurface point openHist sectionA germA ringEndpoint ->
      RingedSpaceSingletonSurface point openHist sectionB germB ringEndpoint ->
        hsame germA germB -> hsame openHist restrictedOpen ->
          Cont restrictedOpen sectionA restrictedGermA ->
            Cont restrictedOpen sectionB restrictedGermB ->
              CommRingSingletonClassifier chartA chartB ->
                SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
                    restrictedOpen sectionB restrictedGermB restrictedOpen ∧
                  CommRingSingletonClassifier chartA chartB ∧
                    RingedSpaceSingletonSurface point openHist sectionA germA ringEndpoint ∧
                      RingedSpaceSingletonSurface point openHist sectionB germB ringEndpoint := by
  intro surfaceA surfaceB sameGerm sameOpen restrictedA restrictedB chartClassifier
  have comparison :
      SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
        restrictedOpen sectionB restrictedGermB restrictedOpen :=
    SheafBHistPointGermComparison_restricted_open_descent
      surfaceA.right.left surfaceB.right.left sameGerm sameOpen restrictedA restrictedB
  exact And.intro comparison
    (And.intro chartClassifier
      (And.intro surfaceA surfaceB))

theorem SchemeAffineCoverLedger_exactness_obligation
    {point openHist sectionHist germ ringEndpoint chartEndpoint : BHist} :
    RingedSpaceSingletonSurface point openHist sectionHist germ ringEndpoint ->
      CommRingSingletonClassifier ringEndpoint chartEndpoint ->
        SheafBHistPointGermLedger point openHist sectionHist germ ∧
          Cont openHist sectionHist germ ∧
            CommRingSingletonCarrier ringEndpoint ∧
              CommRingSingletonCarrier chartEndpoint ∧
                hsame ringEndpoint chartEndpoint ∧ TopologySingletonOpenAt openHist point := by
  intro surface chartClassifier
  exact And.intro surface.right.left
    (And.intro surface.right.left.right.right
      (And.intro chartClassifier.left
        (And.intro chartClassifier.right.left
          (And.intro chartClassifier.right.right surface.left))))

theorem SchemeAffineCoverLedger_restriction_exactness
    {point openHist restrictedOpen sectionHist germ restrictedGerm ringEndpoint
      chartEndpoint : BHist} :
    RingedSpaceSingletonSurface point openHist sectionHist germ ringEndpoint ->
      hsame openHist restrictedOpen ->
        Cont restrictedOpen sectionHist restrictedGerm ->
          CommRingSingletonClassifier chartEndpoint BHist.Empty ->
            RingedSpaceSingletonSurface point restrictedOpen sectionHist restrictedGerm
              chartEndpoint ∧ hsame germ restrictedGerm ∧
                CommRingSingletonClassifier ringEndpoint chartEndpoint := by
  intro surface sameOpen restrictedRow chartClassifier
  have ringClassifier : CommRingSingletonClassifier ringEndpoint chartEndpoint :=
    And.intro surface.right.right.left
      (And.intro chartClassifier.left
        (hsame_trans surface.right.right.right.right (hsame_symm chartClassifier.right.right)))
  have restricted :
      RingedSpaceSingletonSurface point restrictedOpen sectionHist restrictedGerm chartEndpoint ∧
        hsame germ restrictedGerm ∧ CommRingSingletonClassifier chartEndpoint BHist.Empty :=
    RingedSpaceSingletonSurface_restriction_exact_ledger
      surface sameOpen restrictedRow ringClassifier
  exact And.intro restricted.left (And.intro restricted.right.left ringClassifier)

theorem SchemeAffineCoverLedger_overlap_classifier_locality
    {point openA openB sectionA sectionB germA germB ringA ringB chartA chartB common :
      BHist} :
    RingedSpaceSingletonSurface point openA sectionA germA ringA ->
      RingedSpaceSingletonSurface point openB sectionB germB ringB ->
        SheafBHistPointGermComparison point openA sectionA germA openB sectionB germB
          common ->
          CommRingSingletonClassifier ringA chartA ->
            CommRingSingletonClassifier ringB chartB ->
              CommRingSingletonClassifier chartA chartB ∧ Cont common sectionA germA ∧
                Cont common sectionB germB ∧ hsame germA germB := by
  intro surfaceA surfaceB comparison chartAClassified chartBClassified
  have ringAEmpty : hsame ringA BHist.Empty := surfaceA.right.right.right.right
  have ringBEmpty : hsame ringB BHist.Empty := surfaceB.right.right.right.right
  have sameCharts : hsame chartA chartB :=
    hsame_trans (hsame_symm chartAClassified.right.right)
      (hsame_trans ringAEmpty
        (hsame_trans (hsame_symm ringBEmpty) chartBClassified.right.right))
  exact And.intro
    (And.intro chartAClassified.right.left
      (And.intro chartBClassified.right.left sameCharts))
      (And.intro comparison.right.right.right.right.right.right.left
        (And.intro comparison.right.right.right.right.right.right.right.left
          comparison.right.right.right.right.right.right.right.right))

theorem SchemeAffineCoverLedger_restricted_global_soundness
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB globalA globalB ringEndpoint operationA operationB : BHist} :
    RingedSpaceSingletonSurface point openHist sectionA germA ringEndpoint ->
      SheafBHistPointGermLedger point openHist sectionB germB ->
        hsame germA germB -> hsame openHist restrictedOpen ->
          Cont restrictedOpen sectionA restrictedGermA ->
            Cont restrictedOpen sectionB restrictedGermB ->
              Cont restrictedOpen sectionA globalA ->
                Cont restrictedOpen sectionB globalB ->
                  CommRingSingletonClassifier operationA operationB ->
                    hsame globalA globalB ∧
                      CommRingSingletonClassifier operationA operationB ∧
                        RingedSpaceSingletonSurface point openHist sectionA germA
                          ringEndpoint := by
  intro surface ledgerB sameGerm sameOpen restrictedA restrictedB globalACont globalBCont
    commOps
  have sameGlobal :
      hsame globalA globalB :=
    SheafBHistPointGermComparison_restricted_global_soundness
      surface.right.left ledgerB sameGerm sameOpen restrictedA restrictedB globalACont globalBCont
      (cont_deterministic restrictedA globalACont) (cont_deterministic restrictedB globalBCont)
  exact And.intro sameGlobal (And.intro commOps surface)

end BEDC.Derived.SchemeUp
