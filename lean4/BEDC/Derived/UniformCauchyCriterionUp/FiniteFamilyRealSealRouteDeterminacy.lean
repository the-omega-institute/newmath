import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_finite_family_real_seal_route_determinacy
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name sealRead
      sealRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont tail sealRow sealRead ->
        Cont tail sealRow sealRead' ->
          PkgSig bundle sealRead pkg ->
            PkgSig bundle sealRead' pkg ->
              UnaryHistory sealRead ∧ UnaryHistory sealRead' ∧ hsame sealRead sealRead' ∧
                Cont index windows modulus ∧ Cont modulus tolerance tail ∧
                  Cont tail sealRow sealRead ∧ Cont tail sealRow sealRead' ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle sealRead pkg ∧
                      PkgSig bundle sealRead' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet tailSealRead tailSealRead' sealPkg sealPkg'
  obtain ⟨_indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    indexWindowsModulus, modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  have sealReadUnary' : UnaryHistory sealRead' :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead'
  have sameSealRead : hsame sealRead sealRead' :=
    cont_deterministic tailSealRead tailSealRead'
  exact
    ⟨sealReadUnary, sealReadUnary', sameSealRead, indexWindowsModulus,
      modulusToleranceTail, tailSealRead, tailSealRead', namePkg, sealPkg, sealPkg'⟩

end BEDC.Derived.UniformCauchyCriterionUp
