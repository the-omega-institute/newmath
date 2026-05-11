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

def CauchyModulusCarrier
    (precision threshold tolerance observation ledger r01 r12 r123 window packet : BHist) :
    Prop :=
  UnaryHistory precision ∧ UnaryHistory threshold ∧ Cont precision threshold r01 ∧
    Cont r01 tolerance r12 ∧ Cont r12 observation r123 ∧ Cont r123 ledger window ∧
      hsame packet window

theorem CauchyModulusCarrier_finite_window_closure
    {precision threshold tolerance observation ledger r01 r12 r123 window packet : BHist}
    (hC :
      CauchyModulusCarrier precision threshold tolerance observation ledger r01 r12 r123
        window packet) :
    Cont precision (append threshold (append tolerance (append observation ledger))) packet ∧
      hsame packet window := by
  have precisionThreshold : Cont precision threshold r01 :=
    hC.right.right.left
  have thresholdTolerance : Cont r01 tolerance r12 :=
    hC.right.right.right.left
  have toleranceObservation : Cont r12 observation r123 :=
    hC.right.right.right.right.left
  have observationLedger : Cont r123 ledger window :=
    hC.right.right.right.right.right.left
  have packetWindow : hsame packet window :=
    hC.right.right.right.right.right.right
  cases precisionThreshold
  cases thresholdTolerance
  cases toleranceObservation
  cases observationLedger
  cases packetWindow
  constructor
  · exact
      (append_assoc (append (append precision threshold) tolerance) observation ledger).trans
        ((append_assoc (append precision threshold) tolerance (append observation ledger)).trans
          (append_assoc precision threshold (append tolerance (append observation ledger))))
  · rfl

end BEDC.Derived.CauchyModulusUp
