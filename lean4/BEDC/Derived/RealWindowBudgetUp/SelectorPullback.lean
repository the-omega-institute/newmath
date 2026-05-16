import BEDC.Derived.RealWindowBudgetUp

namespace BEDC.Derived.RealWindowBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealWindowBudgetCarrier_selector_disclosure_readback_scope [AskSetup] [PackageSetup]
    {request windows dyadic handoff realSeal selector disclosure transport route provenance
      nameRow selectorRead disclosureRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealWindowBudgetCarrier request windows dyadic handoff realSeal selector disclosure
        transport route provenance nameRow bundle pkg →
      Cont selector disclosure selectorRead →
        Cont selectorRead route disclosureRead →
          Cont handoff realSeal endpoint →
            PkgSig bundle disclosureRead pkg →
              UnaryHistory selectorRead ∧ UnaryHistory disclosureRead ∧
                UnaryHistory endpoint ∧ Cont selector disclosure selectorRead ∧
                  Cont selectorRead route disclosureRead ∧ Cont handoff realSeal endpoint ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle disclosureRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier selectorDisclosureRead selectorReadRouteDisclosure handoffRealSealEndpoint
    disclosurePkg
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed carrier.selector_unary carrier.disclosure_unary selectorDisclosureRead
  have disclosureReadUnary : UnaryHistory disclosureRead :=
    unary_cont_closed selectorReadUnary carrier.route_unary selectorReadRouteDisclosure
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed carrier.handoff_unary carrier.realSeal_unary handoffRealSealEndpoint
  exact
    ⟨selectorReadUnary, disclosureReadUnary, endpointUnary, selectorDisclosureRead,
      selectorReadRouteDisclosure, handoffRealSealEndpoint, carrier.provenance_pkg,
      disclosurePkg⟩

end BEDC.Derived.RealWindowBudgetUp
