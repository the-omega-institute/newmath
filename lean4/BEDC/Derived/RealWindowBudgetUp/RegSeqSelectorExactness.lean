import BEDC.Derived.RealWindowBudgetUp

namespace BEDC.Derived.RealWindowBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealWindowBudgetCarrier_regseq_selector_exactness [AskSetup] [PackageSetup]
    {request windows dyadic handoff realSeal selector disclosure transport route provenance
      nameRow selectorRead disclosureRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealWindowBudgetCarrier request windows dyadic handoff realSeal selector disclosure
        transport route provenance nameRow bundle pkg →
      Cont request selector selectorRead →
        Cont selectorRead disclosure disclosureRead →
          PkgSig bundle disclosureRead pkg →
            UnaryHistory request ∧ UnaryHistory windows ∧ UnaryHistory dyadic ∧
              UnaryHistory handoff ∧ UnaryHistory selector ∧ UnaryHistory disclosure ∧
                UnaryHistory selectorRead ∧ UnaryHistory disclosureRead ∧
                  Cont request windows dyadic ∧ Cont dyadic handoff realSeal ∧
                    Cont request selector selectorRead ∧
                      Cont selectorRead disclosure disclosureRead ∧
                        Cont selector disclosure transport ∧ Cont transport route nameRow ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle nameRow pkg ∧
                            PkgSig bundle disclosureRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig
  intro carrier requestSelector selectorDisclosure disclosurePkg
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed carrier.request_unary carrier.selector_unary requestSelector
  have disclosureReadUnary : UnaryHistory disclosureRead :=
    unary_cont_closed selectorReadUnary carrier.disclosure_unary selectorDisclosure
  exact
    ⟨carrier.request_unary, carrier.windows_unary, carrier.dyadic_unary,
      carrier.handoff_unary, carrier.selector_unary, carrier.disclosure_unary,
      selectorReadUnary, disclosureReadUnary, carrier.request_windows_dyadic,
      carrier.dyadic_handoff_realSeal, requestSelector, selectorDisclosure,
      carrier.selector_disclosure_transport, carrier.transport_route_nameRow,
      carrier.provenance_pkg, carrier.nameRow_pkg, disclosurePkg⟩

end BEDC.Derived.RealWindowBudgetUp
