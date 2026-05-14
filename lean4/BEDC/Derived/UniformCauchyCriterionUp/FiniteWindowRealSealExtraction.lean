import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_finite_window_real_seal_extraction [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name windowRead
      sealRead realExtract : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont windows tail windowRead →
        Cont tail sealRow sealRead →
          Cont windowRead sealRead realExtract →
            PkgSig bundle windowRead pkg →
              PkgSig bundle sealRead pkg →
                PkgSig bundle realExtract pkg →
                  UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
                    UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
                      UnaryHistory windowRead ∧ UnaryHistory sealRead ∧
                        UnaryHistory realExtract ∧ Cont index windows modulus ∧
                          Cont modulus tolerance tail ∧ Cont windows tail windowRead ∧
                            Cont tail sealRow sealRead ∧
                              Cont windowRead sealRead realExtract ∧ PkgSig bundle name pkg ∧
                                PkgSig bundle windowRead pkg ∧ PkgSig bundle sealRead pkg ∧
                                  PkgSig bundle realExtract pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet windowsTailRead tailSealRead windowSealReal windowReadPkg sealReadPkg realPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed windowsUnary tailUnary windowsTailRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  have realExtractUnary : UnaryHistory realExtract :=
    unary_cont_closed windowReadUnary sealReadUnary windowSealReal
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      windowReadUnary, sealReadUnary, realExtractUnary, indexWindowsModulus, modulusToleranceTail,
      windowsTailRead, tailSealRead, windowSealReal, namePkg, windowReadPkg, sealReadPkg,
      realPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
