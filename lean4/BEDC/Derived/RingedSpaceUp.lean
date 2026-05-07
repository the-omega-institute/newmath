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
