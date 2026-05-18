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

theorem UniformCauchyCriterionFiniteWindowRealSealExtraction [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name
      windowToleranceRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont windows tolerance windowToleranceRead ->
        hsame windowToleranceRead tail ->
          Cont tail sealRow sealRead ->
            PkgSig bundle sealRead pkg ->
              UnaryHistory windows ∧ UnaryHistory tolerance ∧ UnaryHistory tail ∧
                UnaryHistory sealRow ∧ UnaryHistory windowToleranceRead ∧
                  UnaryHistory sealRead ∧ Cont windows tolerance windowToleranceRead ∧
                    hsame windowToleranceRead tail ∧ Cont tail sealRow sealRead ∧
                      PkgSig bundle name pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet windowsToleranceRead windowToleranceTail tailSealRead sealReadPkg
  obtain ⟨_indexUnary, windowsUnary, _modulusUnary, toleranceUnary, tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have windowToleranceUnary : UnaryHistory windowToleranceRead :=
    unary_cont_closed windowsUnary toleranceUnary windowsToleranceRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  exact
    ⟨windowsUnary, toleranceUnary, tailUnary, sealRowUnary, windowToleranceUnary,
      sealReadUnary, windowsToleranceRead, windowToleranceTail, tailSealRead, namePkg,
      sealReadPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
