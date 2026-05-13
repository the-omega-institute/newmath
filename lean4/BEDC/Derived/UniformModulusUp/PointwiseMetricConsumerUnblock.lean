import BEDC.Derived.UniformModulusUp

namespace BEDC.Derived.UniformModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformModulusPacket_pointwise_metric_consumer_unblock [AskSetup] [PackageSetup]
    {tolerance precision bundleRow radius coverage pointwise foldLedger transport provenance
      nameRow realized distance consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformModulusPacket tolerance precision bundleRow radius coverage pointwise foldLedger
        transport provenance nameRow bundle pkg →
      UnaryHistory pointwise →
        Cont tolerance bundleRow coverage →
          Cont precision radius foldLedger →
            Cont foldLedger nameRow realized →
              Cont coverage pointwise distance →
                Cont distance foldLedger consumer →
                  PkgSig bundle realized pkg →
                    PkgSig bundle consumer pkg →
                      UnaryHistory coverage ∧ UnaryHistory foldLedger ∧
                        UnaryHistory realized ∧ UnaryHistory distance ∧
                          UnaryHistory consumer ∧ Cont foldLedger nameRow realized ∧
                            Cont coverage pointwise distance ∧
                              Cont distance foldLedger consumer ∧
                                PkgSig bundle realized pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg
  intro packet pointwiseUnary coverageRoute foldRoute realizedRoute distanceRoute
    consumerRoute realizedPkg consumerPkg
  obtain ⟨toleranceUnary, precisionUnary, _bundleRowUnary, radiusUnary, nameRowUnary,
    packetCoverageRoute, _transportRoute, packetFoldRoute, _provenanceRoute, _packetPkg⟩ :=
    packet
  have coverageUnary : UnaryHistory coverage :=
    unary_cont_closed toleranceUnary _bundleRowUnary coverageRoute
  have foldLedgerUnary : UnaryHistory foldLedger :=
    unary_cont_closed precisionUnary radiusUnary foldRoute
  have realizedUnary : UnaryHistory realized :=
    unary_cont_closed foldLedgerUnary nameRowUnary realizedRoute
  have distanceUnary : UnaryHistory distance :=
    unary_cont_closed coverageUnary pointwiseUnary distanceRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed distanceUnary foldLedgerUnary consumerRoute
  exact
    ⟨coverageUnary, foldLedgerUnary, realizedUnary, distanceUnary, consumerUnary,
      realizedRoute, distanceRoute, consumerRoute, realizedPkg, consumerPkg⟩

end BEDC.Derived.UniformModulusUp
