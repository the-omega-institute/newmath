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

def CauchyModulusTailWindow
    (packet precision threshold tolerance schedule ledger pkg : BHist) : Prop :=
  UnaryHistory precision ∧
    UnaryHistory threshold ∧
      PositiveUnaryDenominator tolerance ∧
        Cont threshold tolerance schedule ∧ Cont schedule ledger packet ∧ hsame pkg packet

theorem CauchyModulusTailWindow_smaller_tolerance_transport
    {packet precision threshold tolerance schedule ledger pkg tolerance2 : BHist} :
    CauchyModulusTailWindow packet precision threshold tolerance schedule ledger pkg ->
      PositiveUnaryDenominator tolerance2 -> hsame tolerance tolerance2 ->
        exists schedule2 : BHist, exists packet2 : BHist,
          CauchyModulusTailWindow packet2 precision threshold tolerance2 schedule2 ledger pkg /\
            hsame schedule schedule2 /\ Cont schedule2 ledger packet2 := by
  intro window tolerance2Positive sameTolerance
  have transportedSchedule : Cont threshold tolerance2 schedule :=
    cont_hsame_transport (hsame_refl threshold) sameTolerance (hsame_refl schedule)
      window.right.right.right.left
  exact Exists.intro schedule
    (Exists.intro packet
      (And.intro
        (And.intro window.left
          (And.intro window.right.left
            (And.intro tolerance2Positive
              (And.intro transportedSchedule
                (And.intro window.right.right.right.right.left
                  window.right.right.right.right.right)))))
        (And.intro (hsame_refl schedule) window.right.right.right.right.left)))

end BEDC.Derived.CauchyModulusUp
