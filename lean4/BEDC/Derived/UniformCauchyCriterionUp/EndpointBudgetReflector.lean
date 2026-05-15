import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_finite_family_endpoint_budget_reflector [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name endpointRead
      tailRead sealRead budgetRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index name endpointRead ->
        Cont endpointRead tail tailRead ->
          Cont tail sealRow sealRead ->
            Cont tailRead sealRead budgetRoute ->
              PkgSig bundle budgetRoute pkg ->
                UnaryHistory index ∧ UnaryHistory name ∧ UnaryHistory endpointRead ∧
                  UnaryHistory tailRead ∧ UnaryHistory sealRead ∧ UnaryHistory budgetRoute ∧
                    Cont index windows modulus ∧ Cont modulus tolerance tail ∧
                      Cont index name endpointRead ∧ Cont endpointRead tail tailRead ∧
                        Cont tail sealRow sealRead ∧ Cont tailRead sealRead budgetRoute ∧
                          PkgSig bundle name pkg ∧ PkgSig bundle budgetRoute pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet endpointRoute tailRoute sealRoute budgetRouteCont budgetPkg
  obtain ⟨indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, nameUnary,
    indexWindowsModulus, modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed indexUnary nameUnary endpointRoute
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed endpointUnary tailUnary tailRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary sealRoute
  have budgetUnary : UnaryHistory budgetRoute :=
    unary_cont_closed tailReadUnary sealReadUnary budgetRouteCont
  exact
    ⟨indexUnary, nameUnary, endpointUnary, tailReadUnary, sealReadUnary, budgetUnary,
      indexWindowsModulus, modulusToleranceTail, endpointRoute, tailRoute, sealRoute,
      budgetRouteCont, namePkg, budgetPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
