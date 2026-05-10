import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.StackUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem StackCarrierPacket_public_surface [AskSetup] [PackageSetup]
    {site sheaf object arrow transport restriction provenance carrier endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory site ->
      UnaryHistory sheaf ->
        UnaryHistory object ->
          UnaryHistory arrow ->
            UnaryHistory transport ->
              UnaryHistory restriction ->
                UnaryHistory provenance ->
                  Cont site sheaf carrier ->
                    Cont object arrow transport ->
                      Cont carrier restriction endpoint ->
                        PkgSig bundle endpoint pkg ->
                          UnaryHistory carrier ∧ UnaryHistory endpoint ∧
                            hsame carrier (append site sheaf) ∧
                              hsame transport (append object arrow) ∧
                                hsame endpoint (append carrier restriction) ∧
                                  PkgSig bundle endpoint pkg := by
  intro siteUnary sheafUnary objectUnary arrowUnary _ restrictionUnary _ siteSheafCarrier
  intro objectArrowTransport carrierRestrictionEndpoint endpointPkg
  have carrierUnary : UnaryHistory carrier :=
    unary_cont_closed siteUnary sheafUnary siteSheafCarrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed carrierUnary restrictionUnary carrierRestrictionEndpoint
  exact And.intro carrierUnary
    (And.intro endpointUnary
      (And.intro siteSheafCarrier
        (And.intro objectArrowTransport
          (And.intro carrierRestrictionEndpoint endpointPkg))))

end BEDC.Derived.StackUp
