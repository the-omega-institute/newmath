import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_shared_window_obligation [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name toleranceRead
      tailRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont modulus tolerance toleranceRead ->
        Cont tolerance tail tailRead ->
          Cont tail sealRow sealRead ->
            PkgSig bundle toleranceRead pkg ->
              PkgSig bundle tailRead pkg ->
                PkgSig bundle sealRead pkg ->
                  UnaryHistory windows ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
                    UnaryHistory toleranceRead ∧ UnaryHistory tailRead ∧ UnaryHistory sealRead ∧
                      Cont index windows modulus ∧ Cont modulus tolerance tail ∧
                        Cont modulus tolerance toleranceRead ∧ Cont tolerance tail tailRead ∧
                          Cont tail sealRow sealRead ∧ PkgSig bundle name pkg ∧
                            PkgSig bundle toleranceRead pkg ∧ PkgSig bundle tailRead pkg ∧
                              PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet modulusToleranceRead toleranceTailRead tailSealRead toleranceReadPkg tailReadPkg
    sealReadPkg
  obtain ⟨_indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed modulusUnary toleranceUnary modulusToleranceRead
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed toleranceUnary tailUnary toleranceTailRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  exact
    ⟨windowsUnary, modulusUnary, toleranceUnary, toleranceReadUnary, tailReadUnary,
      sealReadUnary, indexWindowsModulus, modulusToleranceTail, modulusToleranceRead,
      toleranceTailRead, tailSealRead, namePkg, toleranceReadPkg, tailReadPkg, sealReadPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
