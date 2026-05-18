import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_finite_envelope_route_determinacy
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name windowRead
      windowRead' sealRead sealRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont windows tail windowRead ->
        Cont windows tail windowRead' ->
          hsame windowRead windowRead' ->
            Cont windowRead sealRow sealRead ->
              Cont windowRead' sealRow sealRead' ->
                PkgSig bundle sealRead pkg ->
                  PkgSig bundle sealRead' pkg ->
                    hsame sealRead sealRead' ∧ UnaryHistory windowRead ∧
                      UnaryHistory windowRead' ∧ UnaryHistory sealRead ∧
                        UnaryHistory sealRead' ∧ PkgSig bundle name pkg ∧
                          PkgSig bundle sealRead pkg ∧ PkgSig bundle sealRead' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet windowsTailRead windowsTailRead' sameWindowRead windowSealRead
    windowSealRead' sealPkg sealPkg'
  obtain ⟨_indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed windowsUnary tailUnary windowsTailRead
  have windowReadUnary' : UnaryHistory windowRead' :=
    unary_cont_closed windowsUnary tailUnary windowsTailRead'
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed windowReadUnary sealRowUnary windowSealRead
  have sealReadUnary' : UnaryHistory sealRead' :=
    unary_cont_closed windowReadUnary' sealRowUnary windowSealRead'
  have sameSealRead : hsame sealRead sealRead' :=
    cont_respects_hsame sameWindowRead (hsame_refl sealRow) windowSealRead windowSealRead'
  exact
    ⟨sameSealRead, windowReadUnary, windowReadUnary', sealReadUnary, sealReadUnary',
      namePkg, sealPkg, sealPkg'⟩

end BEDC.Derived.UniformCauchyCriterionUp
