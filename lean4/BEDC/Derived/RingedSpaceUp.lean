import BEDC.Derived.CommRingUp
import BEDC.Derived.SheafUp
import BEDC.Derived.TopologyUp.Singleton

namespace BEDC.Derived.RingedSpaceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.CommRingUp
open BEDC.Derived.SheafUp
open BEDC.Derived.TopologyUp

theorem RingedSpaceSingleton_cover_nerve_empty_boundary
    {point ambient member overlap route germ operationA operationB : BHist} :
    TopologySingletonOpenAt BHist.Empty point ->
      SheafBHistCoverNerveLedger ambient member overlap route germ ->
        hsame germ BHist.Empty ->
          CommRingSingletonClassifier operationA operationB ->
            hsame overlap BHist.Empty ∧ hsame route BHist.Empty ∧
              CommRingSingletonClassifier operationA operationB ∧
                TopologySingletonOpenAt BHist.Empty point := by
  intro openPoint ledger germEmpty commOps
  have boundary := SheafBHistCoverNerveLedger_empty_boundary ledger germEmpty
  exact And.intro boundary.left
    (And.intro boundary.right
      (And.intro commOps openPoint))

def RingedSpaceSingletonPackage
    (point openHist sectionHist germ ringEndpoint : BHist) : Prop :=
  SheafBHistPointGermLedger point openHist sectionHist germ ∧
    CommRingSingletonCarrier sectionHist ∧
      CommRingSingletonClassifier sectionHist ringEndpoint

theorem RingedSpaceSingleton_carrier_sheaf_obligation
    {point openHist sectionHist germ ringEndpoint : BHist} :
    RingedSpaceSingletonPackage point openHist sectionHist germ ringEndpoint ->
      UnaryHistory point ∧ UnaryHistory openHist ∧ Cont openHist sectionHist germ ∧
        CommRingSingletonCarrier sectionHist ∧ CommRingSingletonCarrier ringEndpoint ∧
          hsame sectionHist ringEndpoint := by
  intro package
  exact And.intro package.left.left
    (And.intro package.left.right.left
      (And.intro package.left.right.right
        (And.intro package.right.left
          (And.intro package.right.right.right.left package.right.right.right.right))))

def RingedSpaceSingletonSurface
    (point openHist sectionHist germ ringEndpoint : BHist) : Prop :=
  TopologySingletonOpenAt openHist point ∧
    SheafBHistPointGermLedger point openHist sectionHist germ ∧
      CommRingSingletonClassifier ringEndpoint BHist.Empty

theorem RingedSpaceSingletonSurface_carrier_classifier_rows
    {point openHist sectionHist germ ringEndpoint : BHist} :
    RingedSpaceSingletonSurface point openHist sectionHist germ ringEndpoint ->
      TopologySingletonCarrier point ∧ UnaryHistory point ∧ UnaryHistory openHist ∧
        Cont openHist sectionHist germ ∧ CommRingSingletonCarrier ringEndpoint ∧
          CommRingSingletonClassifier ringEndpoint BHist.Empty := by
  intro surface
  exact And.intro surface.left.right
      (And.intro surface.right.left.left
        (And.intro surface.right.left.right.left
          (And.intro surface.right.left.right.right
            (And.intro surface.right.right.left surface.right.right))))

theorem RingedSpaceSingletonSurface_restriction_exact_ledger
    {point openHist restrictedOpen sectionHist germ restrictedGerm ringEndpoint
      ringEndpoint' : BHist} :
    RingedSpaceSingletonSurface point openHist sectionHist germ ringEndpoint ->
      hsame openHist restrictedOpen ->
        Cont restrictedOpen sectionHist restrictedGerm ->
          CommRingSingletonClassifier ringEndpoint ringEndpoint' ->
            RingedSpaceSingletonSurface point restrictedOpen sectionHist restrictedGerm
              ringEndpoint' ∧ hsame germ restrictedGerm ∧
                CommRingSingletonClassifier ringEndpoint' BHist.Empty := by
  intro surface sameOpen restrictedRow commAligned
  have sheafReadback :
      SheafBHistPointGermLedger point restrictedOpen sectionHist restrictedGerm ∧
        hsame germ restrictedGerm :=
    SheafBHistPointGermLedger_restriction_readback surface.right.left sameOpen restrictedRow
  cases sameOpen
  have restrictedTopology : TopologySingletonOpenAt openHist point := surface.left
  have endpointEmpty : CommRingSingletonClassifier ringEndpoint' BHist.Empty :=
    And.intro commAligned.right.left
      (And.intro (hsame_refl BHist.Empty) commAligned.right.left)
  exact And.intro
    (And.intro restrictedTopology (And.intro sheafReadback.left endpointEmpty))
    (And.intro sheafReadback.right endpointEmpty)

theorem RingedSpaceSingleton_sheaf_commring_stalk_locality_obligation
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB operationA operationB : BHist} :
    TopologySingletonOpenAt BHist.Empty point ->
      SheafBHistPointGermLedger point openHist sectionA germA ->
        SheafBHistPointGermLedger point openHist sectionB germB ->
          hsame germA germB -> hsame openHist restrictedOpen ->
            Cont restrictedOpen sectionA restrictedGermA ->
              Cont restrictedOpen sectionB restrictedGermB ->
                CommRingSingletonClassifier operationA operationB ->
                  SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
                    SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
                      hsame restrictedGermA restrictedGermB ∧
                        CommRingSingletonClassifier operationA operationB ∧
                          TopologySingletonOpenAt BHist.Empty point := by
  intro openPoint ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB commOps
  have descent :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          hsame restrictedGermA restrictedGermB :=
    SheafRestrictedOpenCarrier_locality_gluing_descent
      ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB
  exact And.intro descent.left
      (And.intro descent.right.left
        (And.intro descent.right.right
          (And.intro commOps openPoint)))

theorem RingedSpaceSingleton_stability_ledger_obligation
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB ringEndpoint operationA operationB : BHist} :
    RingedSpaceSingletonSurface point openHist sectionA germA ringEndpoint ->
      RingedSpaceSingletonSurface point openHist sectionB germB ringEndpoint ->
        hsame germA germB -> hsame openHist restrictedOpen ->
          Cont restrictedOpen sectionA restrictedGermA ->
            Cont restrictedOpen sectionB restrictedGermB ->
              CommRingSingletonClassifier operationA operationB ->
                SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
                  SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
                    hsame restrictedGermA restrictedGermB ∧
                      CommRingSingletonClassifier operationA operationB ∧
                        TopologySingletonOpenAt openHist point ∧
                          CommRingSingletonCarrier ringEndpoint := by
  intro surfaceA surfaceB sameGerm sameOpen restrictedA restrictedB commOps
  have descent :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          hsame restrictedGermA restrictedGermB :=
    SheafRestrictedOpenCarrier_locality_gluing_descent
      surfaceA.right.left surfaceB.right.left sameGerm sameOpen restrictedA restrictedB
  exact And.intro descent.left
    (And.intro descent.right.left
      (And.intro descent.right.right
        (And.intro commOps
          (And.intro surfaceA.left surfaceA.right.right.left))))

theorem RingedSpaceSingleton_stalk_restriction_commring_stability
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB ringEndpoint : BHist} :
    RingedSpaceSingletonSurface point openHist sectionA germA ringEndpoint ->
      SheafBHistPointGermLedger point openHist sectionB germB ->
        hsame germA germB ->
          hsame openHist restrictedOpen ->
            Cont restrictedOpen sectionA restrictedGermA ->
              Cont restrictedOpen sectionB restrictedGermB ->
                CommRingSingletonClassifier ringEndpoint BHist.Empty ->
                  SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
                    SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
                      hsame restrictedGermA restrictedGermB ∧
                        CommRingSingletonClassifier ringEndpoint BHist.Empty ∧
                          TopologySingletonOpenAt BHist.Empty point := by
  intro surface ledgerB sameGerm sameOpen restrictedA restrictedB commRing
  have descent :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          hsame restrictedGermA restrictedGermB :=
    SheafRestrictedOpenCarrier_locality_gluing_descent
      surface.right.left ledgerB sameGerm sameOpen restrictedA restrictedB
  have openPoint : TopologySingletonOpenAt BHist.Empty point :=
    And.intro (hsame_refl BHist.Empty) surface.left.right
  exact And.intro descent.left
    (And.intro descent.right.left
      (And.intro descent.right.right
        (And.intro commRing openPoint)))

theorem RingedSpaceSingleton_stalk_locality_obligation
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA restrictedGermB
      operationA operationB tail : BHist} :
    RingedSpaceSingletonSurface point openHist sectionA germA operationA ->
      RingedSpaceSingletonPackage point openHist sectionB germB operationB ->
        hsame germA germB -> hsame openHist restrictedOpen ->
          Cont restrictedOpen sectionA restrictedGermA ->
            Cont restrictedOpen sectionB restrictedGermB ->
              (hsame restrictedOpen (BHist.e0 tail) -> False) ∧
                SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
                  SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
                    hsame restrictedGermA restrictedGermB ∧
                      CommRingSingletonClassifier operationA BHist.Empty ∧
                        CommRingSingletonCarrier operationB := by
  intro surface package sameGerm sameOpen restrictedA restrictedB
  have descent :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          hsame restrictedGermA restrictedGermB :=
    SheafRestrictedOpenCarrier_locality_gluing_descent
      surface.right.left package.left sameGerm sameOpen restrictedA restrictedB
  have restrictedOpenNotZero : hsame restrictedOpen (BHist.e0 tail) -> False := by
    intro sameZero
    exact unary_no_zero_extension (unary_transport descent.left.right.left sameZero)
  exact And.intro restrictedOpenNotZero
    (And.intro descent.left
        (And.intro descent.right.left
          (And.intro descent.right.right
          (And.intro surface.right.right package.right.right.right.left))))

theorem RingedSpaceSingletonSurface_stalk_locality_common_neighborhood
    {point openHist sectionA sectionB germA germB ringEndpointA ringEndpointB restrictedOpen
      restrictedGermA restrictedGermB : BHist} :
    RingedSpaceSingletonSurface point openHist sectionA germA ringEndpointA ->
      RingedSpaceSingletonSurface point openHist sectionB germB ringEndpointB ->
        hsame germA germB -> hsame openHist restrictedOpen ->
          Cont restrictedOpen sectionA restrictedGermA ->
            Cont restrictedOpen sectionB restrictedGermB ->
              TopologySingletonOpenAt BHist.Empty point ∧
                SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
                  SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
                    hsame restrictedGermA restrictedGermB ∧
                      CommRingSingletonClassifier ringEndpointA ringEndpointB := by
  intro surfaceA surfaceB sameGerm sameOpen restrictedA restrictedB
  have descent :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          hsame restrictedGermA restrictedGermB :=
    SheafRestrictedOpenCarrier_locality_gluing_descent
      surfaceA.right.left surfaceB.right.left sameGerm sameOpen restrictedA restrictedB
  have openPoint : TopologySingletonOpenAt BHist.Empty point :=
    And.intro (hsame_refl BHist.Empty) surfaceA.left.right
  have sameRingEndpoints : hsame ringEndpointA ringEndpointB :=
    hsame_trans surfaceA.right.right.right.right
      (hsame_symm surfaceB.right.right.right.right)
  have ringClassified : CommRingSingletonClassifier ringEndpointA ringEndpointB :=
    And.intro surfaceA.right.right.left
      (And.intro surfaceB.right.right.left sameRingEndpoints)
  exact And.intro openPoint
    (And.intro descent.left
      (And.intro descent.right.left
        (And.intro descent.right.right ringClassified)))

def RingedSpaceRestrictionLedger
    (point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB operationA operationB : BHist) : Prop :=
  TopologySingletonOpenAt restrictedOpen point ∧
    SheafBHistPointGermLedger point openHist sectionA germA ∧
      SheafBHistPointGermLedger point openHist sectionB germB ∧
        hsame germA germB ∧ hsame openHist restrictedOpen ∧
          Cont restrictedOpen sectionA restrictedGermA ∧
            Cont restrictedOpen sectionB restrictedGermB ∧
              CommRingSingletonClassifier operationA operationB

theorem RingedSpaceSingletonSurface_stability_ledger_obligation
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB operationA operationB : BHist} :
    RingedSpaceRestrictionLedger point openHist sectionA sectionB germA germB
        restrictedOpen restrictedGermA restrictedGermB operationA operationB ->
      RingedSpaceSingletonSurface point restrictedOpen sectionA restrictedGermA operationA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          Cont restrictedOpen sectionA restrictedGermA ∧
            Cont restrictedOpen sectionB restrictedGermB ∧
              hsame restrictedGermA restrictedGermB ∧
                CommRingSingletonClassifier operationA operationB ∧
                  TopologySingletonOpenAt restrictedOpen point := by
  intro ledger
  have localized :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          hsame restrictedGermA restrictedGermB ∧
            CommRingSingletonClassifier operationA operationB ∧
              TopologySingletonOpenAt BHist.Empty point :=
    RingedSpaceSingleton_sheaf_commring_stalk_locality_obligation
      (And.intro (hsame_refl BHist.Empty) ledger.left.right)
      ledger.right.left ledger.right.right.left ledger.right.right.right.left
      ledger.right.right.right.right.left ledger.right.right.right.right.right.left
      ledger.right.right.right.right.right.right.left
      ledger.right.right.right.right.right.right.right
  have operationEmpty : CommRingSingletonClassifier operationA BHist.Empty :=
    And.intro localized.right.right.right.left.left
      (And.intro (hsame_refl BHist.Empty) localized.right.right.right.left.left)
  exact And.intro
    (And.intro ledger.left (And.intro localized.left operationEmpty))
    (And.intro localized.right.left
      (And.intro ledger.right.right.right.right.right.left
        (And.intro ledger.right.right.right.right.right.right.left
          (And.intro localized.right.right.left
            (And.intro localized.right.right.right.left ledger.left)))))

theorem RingedSpaceSingletonPackage_stalk_locality_transport
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB ringEndpoint : BHist} :
    RingedSpaceSingletonPackage point openHist sectionA germA ringEndpoint ->
      SheafBHistPointGermLedger point openHist sectionB germB ->
        hsame germA germB -> hsame openHist restrictedOpen ->
          Cont restrictedOpen sectionA restrictedGermA ->
            Cont restrictedOpen sectionB restrictedGermB ->
              RingedSpaceSingletonPackage point restrictedOpen sectionA restrictedGermA
                ringEndpoint ∧
                SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
                  hsame restrictedGermA restrictedGermB := by
  intro package ledgerB sameGerm sameOpen restrictedA restrictedB
  have descent :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          hsame restrictedGermA restrictedGermB :=
    SheafRestrictedOpenCarrier_locality_gluing_descent
      package.left ledgerB sameGerm sameOpen restrictedA restrictedB
  exact And.intro
    (And.intro descent.left (And.intro package.right.left package.right.right))
    (And.intro descent.right.left descent.right.right)

theorem RingedSpaceSingletonSurface_stalk_locality_readback
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB ringEndpoint operationA operationB : BHist} :
    RingedSpaceSingletonSurface point openHist sectionA germA ringEndpoint ->
      SheafBHistPointGermLedger point openHist sectionB germB ->
        hsame germA germB -> hsame openHist restrictedOpen ->
          Cont restrictedOpen sectionA restrictedGermA ->
            Cont restrictedOpen sectionB restrictedGermB ->
              CommRingSingletonClassifier operationA operationB ->
                SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
                  SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
                    hsame restrictedGermA restrictedGermB ∧
                      CommRingSingletonCarrier ringEndpoint ∧
                        CommRingSingletonClassifier operationA operationB := by
  intro surface ledgerB sameGerm sameOpen restrictedA restrictedB commOps
  have descent :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          hsame restrictedGermA restrictedGermB :=
    SheafRestrictedOpenCarrier_locality_gluing_descent
      surface.right.left ledgerB sameGerm sameOpen restrictedA restrictedB
  exact And.intro descent.left
    (And.intro descent.right.left
      (And.intro descent.right.right
        (And.intro surface.right.right.left commOps)))

end BEDC.Derived.RingedSpaceUp
