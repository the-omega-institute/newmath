import BEDC.Derived.RatUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

def CauchyModulusLedgerPacket
    (precision threshold tolerance observation consumption provenance window : BHist) : Prop :=
  UnaryHistory precision ∧ UnaryHistory threshold ∧ RatHistoryCarrier tolerance ∧
    Cont precision threshold window ∧ Cont window tolerance consumption ∧
      Cont consumption observation provenance

theorem CauchyModulusLedgerPacket_hsame_stability
    {precision precision' threshold threshold' tolerance tolerance' observation observation'
      consumption provenance window : BHist} :
    CauchyModulusLedgerPacket precision threshold tolerance observation consumption provenance window ->
      hsame precision' precision -> hsame threshold' threshold -> hsame tolerance' tolerance ->
        hsame observation' observation ->
          exists consumption' provenance' window' : BHist,
            CauchyModulusLedgerPacket precision' threshold' tolerance' observation'
              consumption' provenance' window' ∧
              hsame window window' ∧ hsame consumption consumption' ∧
                hsame provenance provenance' := by
  intro packet samePrecision sameThreshold sameTolerance sameObservation
  cases packet with
  | intro precisionUnary packetRest =>
      cases packetRest with
      | intro thresholdUnary packetRest =>
          cases packetRest with
          | intro toleranceCarrier packetRest =>
              cases packetRest with
              | intro windowRow packetRest =>
                  cases packetRest with
                  | intro consumptionRow provenanceRow =>
                      let window' := append precision' threshold'
                      let consumption' := append window' tolerance'
                      let provenance' := append consumption' observation'
                      have precisionUnary' : UnaryHistory precision' :=
                        unary_transport_symm precisionUnary samePrecision
                      have thresholdUnary' : UnaryHistory threshold' :=
                        unary_transport_symm thresholdUnary sameThreshold
                      have toleranceCarrier' : RatHistoryCarrier tolerance' :=
                        RatHistoryCarrier_hsame_transport (hsame_symm sameTolerance)
                          toleranceCarrier
                      have windowRow' : Cont precision' threshold' window' := by
                        rfl
                      have consumptionRow' : Cont window' tolerance' consumption' := by
                        rfl
                      have provenanceRow' : Cont consumption' observation' provenance' := by
                        rfl
                      have sameWindow : hsame window window' :=
                        cont_respects_hsame (hsame_symm samePrecision)
                          (hsame_symm sameThreshold) windowRow windowRow'
                      have sameConsumption : hsame consumption consumption' :=
                        cont_respects_hsame sameWindow (hsame_symm sameTolerance)
                          consumptionRow consumptionRow'
                      have sameProvenance : hsame provenance provenance' :=
                        cont_respects_hsame sameConsumption (hsame_symm sameObservation)
                          provenanceRow provenanceRow'
                      exact ⟨consumption', provenance', window',
                        ⟨precisionUnary', thresholdUnary', toleranceCarrier', windowRow',
                          consumptionRow', provenanceRow'⟩,
                        sameWindow, sameConsumption, sameProvenance⟩

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

end BEDC.Derived.CauchyModulusUp
