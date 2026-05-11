import BEDC.Derived.ApartnessRealUp

namespace BEDC.Derived.ApartnessRealUp

open BEDC.Derived.RatUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApartnessRealSeparationPacket_mature_consumer_coverage [AskSetup] [PackageSetup]
    {left right radius window leftEndpoint rightEndpoint forwardLedger reverseLedger pkgrow
      metricRow consumerRow scopeRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApartnessRealSeparationPacket left right radius window leftEndpoint rightEndpoint
        forwardLedger reverseLedger pkgrow bundle pkg ->
      UnaryHistory left ->
        UnaryHistory right ->
          UnaryHistory window ->
            UnaryHistory metricRow ->
              Cont pkgrow metricRow consumerRow ->
                Cont pkgrow window scopeRow ->
                  PkgSig bundle consumerRow pkg ->
                    PkgSig bundle scopeRow pkg ->
                      PositiveUnaryDenominator radius ∧ UnaryHistory consumerRow ∧
                        hsame consumerRow (append pkgrow metricRow) ∧
                          Cont pkgrow window scopeRow ∧ PkgSig bundle consumerRow pkg := by
  intro packet leftUnary rightUnary windowUnary metricUnary consumerRowCont scopeRowCont
    consumerPkg _scopePkg
  have consumerBoundary :=
    ApartnessRealSeparationPacket_metric_consumer_separation_boundary packet leftUnary
      rightUnary windowUnary metricUnary consumerRowCont consumerPkg
  exact
    And.intro consumerBoundary.left
      (And.intro consumerBoundary.right.right.right.right.right.right.left
        (And.intro consumerBoundary.right.right.right.right.right.right.right.right.right.left
          (And.intro scopeRowCont consumerPkg)))

end BEDC.Derived.ApartnessRealUp
