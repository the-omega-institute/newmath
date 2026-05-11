import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.RatUp

namespace BEDC.Derived.CauchyModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

def CauchyModulusPacket [AskSetup] [PackageSetup]
    (precision threshold tolerance schedule observationLedger consumptionLedger window
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory threshold ∧ UnaryHistory tolerance ∧
    UnaryHistory schedule ∧ UnaryHistory observationLedger ∧
      UnaryHistory consumptionLedger ∧ UnaryHistory window ∧ UnaryHistory endpoint ∧
        Cont precision threshold schedule ∧ Cont schedule tolerance observationLedger ∧
          Cont observationLedger consumptionLedger window ∧ Cont window threshold endpoint ∧
            PkgSig bundle endpoint pkg

theorem CauchyModulusPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {precision threshold tolerance schedule observationLedger consumptionLedger window endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusPacket precision threshold tolerance schedule observationLedger
      consumptionLedger window endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              CauchyModulusPacket precision threshold tolerance schedule observationLedger
                consumptionLedger window e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              CauchyModulusPacket precision threshold tolerance schedule observationLedger
                consumptionLedger window e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              CauchyModulusPacket precision threshold tolerance schedule observationLedger
                consumptionLedger window e bundle pkg ∧ hsame row e)
          hsame ∧
        Cont precision threshold schedule ∧ Cont schedule tolerance observationLedger ∧
          Cont observationLedger consumptionLedger window ∧ Cont window threshold endpoint ∧
            PkgSig bundle endpoint pkg := by
  intro packet
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro endpoint (Exists.intro endpoint (And.intro packet (hsame_refl endpoint)))
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro row row' same
          exact hsame_symm same
        equiv_trans := by
          intro row row' row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row row' same source
          cases source with
          | intro e data =>
              exact Exists.intro e
                (And.intro data.left (hsame_trans (hsame_symm same) data.right))
      }
      pattern_sound := by
        intro _row source
        exact source
      ledger_sound := by
        intro _row source
        exact source
    }
  · exact
      And.intro packet.right.right.right.right.right.right.right.right.left
        (And.intro packet.right.right.right.right.right.right.right.right.right.left
          (And.intro packet.right.right.right.right.right.right.right.right.right.right.left
            (And.intro packet.right.right.right.right.right.right.right.right.right.right.right.left
              packet.right.right.right.right.right.right.right.right.right.right.right.right)))

def CauchyModulusCarrierPacket
    (precision threshold tolerance observationA observationB ledger provenance : BHist) : Prop :=
  UnaryHistory precision ∧
    UnaryHistory threshold ∧
      PositiveUnaryDenominator tolerance ∧
        UnaryHistory observationA ∧
          UnaryHistory observationB ∧
            UnaryHistory ledger ∧
              UnaryHistory provenance ∧
                Cont precision tolerance threshold ∧
                  Cont threshold observationA ledger ∧
                    Cont ledger provenance observationB

def CauchyModulusClassifierPacket
    (precision threshold tolerance observationA observationB ledger provenance
      precision' threshold' tolerance' observationA' observationB' ledger'
      provenance' : BHist) : Prop :=
  CauchyModulusCarrierPacket precision threshold tolerance observationA observationB ledger
      provenance ∧
    CauchyModulusCarrierPacket precision' threshold' tolerance' observationA' observationB'
        ledger' provenance' ∧
      hsame precision precision' ∧
        hsame threshold threshold' ∧
          hsame tolerance tolerance' ∧
            hsame observationA observationA' ∧
              hsame observationB observationB' ∧
                hsame ledger ledger' ∧
                  hsame provenance provenance'

theorem CauchyModulusPacket_hsame_stability
    {precision threshold tolerance observationA observationB ledger provenance
      precision' threshold' tolerance' observationA' observationB' ledger'
      provenance' : BHist}
    (packet :
      CauchyModulusCarrierPacket precision threshold tolerance observationA observationB ledger
        provenance)
    (samePrecision : hsame precision precision')
    (sameThreshold : hsame threshold threshold')
    (sameTolerance : hsame tolerance tolerance')
    (sameObservationA : hsame observationA observationA')
    (sameObservationB : hsame observationB observationB')
    (sameLedger : hsame ledger ledger')
    (sameProvenance : hsame provenance provenance') :
    CauchyModulusCarrierPacket precision' threshold' tolerance' observationA' observationB'
        ledger' provenance' ∧
      CauchyModulusClassifierPacket precision threshold tolerance observationA observationB ledger
        provenance precision' threshold' tolerance' observationA' observationB' ledger'
        provenance' ∧
        Cont precision' tolerance' threshold' ∧
          Cont threshold' observationA' ledger' ∧
            Cont ledger' provenance' observationB' := by
  have precisionUnary : UnaryHistory precision' :=
    unary_transport packet.left samePrecision
  have thresholdUnary : UnaryHistory threshold' :=
    unary_transport packet.right.left sameThreshold
  have tolerancePositive : PositiveUnaryDenominator tolerance' :=
    PositiveUnaryDenominator_hsame_transport sameTolerance packet.right.right.left
  have observationAUnary : UnaryHistory observationA' :=
    unary_transport packet.right.right.right.left sameObservationA
  have observationBUnary : UnaryHistory observationB' :=
    unary_transport packet.right.right.right.right.left sameObservationB
  have ledgerUnary : UnaryHistory ledger' :=
    unary_transport packet.right.right.right.right.right.left sameLedger
  have provenanceUnary : UnaryHistory provenance' :=
    unary_transport packet.right.right.right.right.right.right.left sameProvenance
  have thresholdRoute : Cont precision' tolerance' threshold' :=
    cont_hsame_transport samePrecision sameTolerance sameThreshold
      packet.right.right.right.right.right.right.right.left
  have ledgerRoute : Cont threshold' observationA' ledger' :=
    cont_hsame_transport sameThreshold sameObservationA sameLedger
      packet.right.right.right.right.right.right.right.right.left
  have observationRoute : Cont ledger' provenance' observationB' :=
    cont_hsame_transport sameLedger sameProvenance sameObservationB
      packet.right.right.right.right.right.right.right.right.right
  have targetPacket :
      CauchyModulusCarrierPacket precision' threshold' tolerance' observationA'
        observationB' ledger' provenance' :=
    And.intro precisionUnary
      (And.intro thresholdUnary
        (And.intro tolerancePositive
          (And.intro observationAUnary
            (And.intro observationBUnary
              (And.intro ledgerUnary
                (And.intro provenanceUnary
                  (And.intro thresholdRoute
                    (And.intro ledgerRoute observationRoute))))))))
  have classified :
      CauchyModulusClassifierPacket precision threshold tolerance observationA observationB ledger
        provenance precision' threshold' tolerance' observationA' observationB' ledger'
        provenance' :=
    And.intro packet
      (And.intro targetPacket
        (And.intro samePrecision
          (And.intro sameThreshold
            (And.intro sameTolerance
              (And.intro sameObservationA
                (And.intro sameObservationB
                  (And.intro sameLedger sameProvenance)))))))
  exact And.intro targetPacket
    (And.intro classified (And.intro thresholdRoute (And.intro ledgerRoute observationRoute)))

end BEDC.Derived.CauchyModulusUp
