import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_finite_window_coverage [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name windowRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont windows tail windowRead ->
        Cont windowRead sealRow sealRead ->
          PkgSig bundle sealRead pkg ->
            UnaryHistory windows ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
              UnaryHistory windowRead ∧ UnaryHistory sealRead ∧ Cont windows tail windowRead ∧
                Cont windowRead sealRow sealRead ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet windowsTailRead windowSealRead sealPkg
  obtain ⟨_indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed windowsUnary tailUnary windowsTailRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed windowReadUnary sealRowUnary windowSealRead
  exact
    ⟨windowsUnary, tailUnary, sealRowUnary, windowReadUnary, sealReadUnary, windowsTailRead,
      windowSealRead, namePkg, sealPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
