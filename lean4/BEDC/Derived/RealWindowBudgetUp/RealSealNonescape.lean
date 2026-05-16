import BEDC.Derived.RealWindowBudgetUp

namespace BEDC.Derived.RealWindowBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealWindowBudgetCarrier_real_seal_nonescape [AskSetup] [PackageSetup]
    {request windows dyadic handoff realSeal selector disclosure transport route provenance
      nameRow sealConsumer visibleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealWindowBudgetCarrier request windows dyadic handoff realSeal selector disclosure transport
        route provenance nameRow bundle pkg ->
      Cont handoff realSeal sealConsumer ->
        Cont selector disclosure visibleRead ->
          PkgSig bundle sealConsumer pkg ->
            PkgSig bundle visibleRead pkg ->
              UnaryHistory request ∧ UnaryHistory windows ∧ UnaryHistory dyadic ∧
                UnaryHistory handoff ∧ UnaryHistory realSeal ∧ UnaryHistory selector ∧
                  UnaryHistory disclosure ∧ UnaryHistory sealConsumer ∧
                    UnaryHistory visibleRead ∧ Cont request windows dyadic ∧
                      Cont dyadic handoff realSeal ∧ Cont handoff realSeal sealConsumer ∧
                        Cont selector disclosure visibleRead ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle sealConsumer pkg ∧ PkgSig bundle visibleRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig
  intro carrier handoffRealSealConsumer selectorDisclosureVisibleRead sealConsumerPkg
    visibleReadPkg
  have sealConsumerUnary : UnaryHistory sealConsumer :=
    unary_cont_closed carrier.handoff_unary carrier.realSeal_unary handoffRealSealConsumer
  have visibleReadUnary : UnaryHistory visibleRead :=
    unary_cont_closed carrier.selector_unary carrier.disclosure_unary selectorDisclosureVisibleRead
  exact
    ⟨carrier.request_unary, carrier.windows_unary, carrier.dyadic_unary,
      carrier.handoff_unary, carrier.realSeal_unary, carrier.selector_unary,
      carrier.disclosure_unary, sealConsumerUnary, visibleReadUnary,
      carrier.request_windows_dyadic, carrier.dyadic_handoff_realSeal,
      handoffRealSealConsumer, selectorDisclosureVisibleRead, carrier.provenance_pkg,
      sealConsumerPkg, visibleReadPkg⟩

end BEDC.Derived.RealWindowBudgetUp
