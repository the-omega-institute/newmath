import BEDC.Derived.RealWindowBudgetUp

namespace BEDC.Derived.RealWindowBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealWindowBudgetCarrier_real_seal_readback_totality [AskSetup] [PackageSetup]
    {request windows dyadic handoff realSeal selector disclosure transport route provenance
      nameRow sealRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealWindowBudgetCarrier request windows dyadic handoff realSeal selector disclosure
        transport route provenance nameRow bundle pkg →
      Cont handoff realSeal sealRead →
        Cont sealRead transport publicRead →
          PkgSig bundle publicRead pkg →
            UnaryHistory request ∧ UnaryHistory windows ∧ UnaryHistory dyadic ∧
              UnaryHistory handoff ∧ UnaryHistory realSeal ∧ UnaryHistory transport ∧
                UnaryHistory sealRead ∧ UnaryHistory publicRead ∧
                  Cont request windows dyadic ∧ Cont dyadic handoff realSeal ∧
                    Cont handoff realSeal sealRead ∧ Cont sealRead transport publicRead ∧
                      Cont transport route nameRow ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle nameRow pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig
  intro carrier handoffSeal sealPublic publicPkg
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed carrier.handoff_unary carrier.realSeal_unary handoffSeal
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed sealReadUnary carrier.transport_unary sealPublic
  exact
    ⟨carrier.request_unary, carrier.windows_unary, carrier.dyadic_unary,
      carrier.handoff_unary, carrier.realSeal_unary, carrier.transport_unary,
      sealReadUnary, publicReadUnary, carrier.request_windows_dyadic,
      carrier.dyadic_handoff_realSeal, handoffSeal, sealPublic,
      carrier.transport_route_nameRow, carrier.provenance_pkg, carrier.nameRow_pkg,
      publicPkg⟩

end BEDC.Derived.RealWindowBudgetUp
