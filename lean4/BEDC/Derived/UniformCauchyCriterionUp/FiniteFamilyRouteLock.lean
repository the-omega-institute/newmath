import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionFiniteFamilyRouteLock [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name windowRead
      thresholdRead tailRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index windows windowRead ->
        Cont windowRead modulus thresholdRead ->
          Cont thresholdRead tolerance tailRead ->
            Cont tailRead sealRow sealRead ->
              PkgSig bundle sealRead pkg ->
                UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
                  UnaryHistory tolerance ∧ UnaryHistory windowRead ∧
                    UnaryHistory thresholdRead ∧ UnaryHistory tailRead ∧
                      UnaryHistory sealRead ∧ Cont index windows windowRead ∧
                        Cont windowRead modulus thresholdRead ∧
                          Cont thresholdRead tolerance tailRead ∧
                            Cont tailRead sealRow sealRead ∧ PkgSig bundle name pkg ∧
                              PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet indexWindowsRead windowModulusThreshold thresholdToleranceTail
    tailSealRead sealReadPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, _tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed indexUnary windowsUnary indexWindowsRead
  have thresholdReadUnary : UnaryHistory thresholdRead :=
    unary_cont_closed windowReadUnary modulusUnary windowModulusThreshold
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed thresholdReadUnary toleranceUnary thresholdToleranceTail
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailReadUnary sealRowUnary tailSealRead
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, windowReadUnary,
      thresholdReadUnary, tailReadUnary, sealReadUnary, indexWindowsRead,
      windowModulusThreshold, thresholdToleranceTail, tailSealRead, namePkg, sealReadPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
