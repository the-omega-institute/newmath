import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_real_completion_synchronizer_terminal_envelope
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name streamRead
      regRead dyadicRead sealRead realRead terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont windows modulus streamRead ->
        Cont streamRead tail regRead ->
          Cont regRead tolerance dyadicRead ->
            Cont dyadicRead sealRow sealRead ->
              Cont sealRead routes realRead ->
                Cont realRead name terminal ->
                  PkgSig bundle terminal pkg ->
                    UnaryHistory windows ∧ UnaryHistory modulus ∧ UnaryHistory streamRead ∧
                      UnaryHistory tail ∧ UnaryHistory regRead ∧ UnaryHistory tolerance ∧
                        UnaryHistory dyadicRead ∧ UnaryHistory sealRow ∧
                          UnaryHistory sealRead ∧ UnaryHistory routes ∧
                            UnaryHistory realRead ∧ UnaryHistory terminal ∧
                              Cont windows modulus streamRead ∧
                                Cont streamRead tail regRead ∧
                                  Cont regRead tolerance dyadicRead ∧
                                    Cont dyadicRead sealRow sealRead ∧
                                      Cont sealRead routes realRead ∧
                                        Cont realRead name terminal ∧
                                          PkgSig bundle name pkg ∧
                                            PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet windowsModulusStream streamTailReg regToleranceDyadic dyadicSealRead
    sealRoutesReal realNameTerminal terminalPkg
  obtain ⟨_indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary,
    sealRowUnary, _transportsUnary, routesUnary, _provenanceUnary, nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed windowsUnary modulusUnary windowsModulusStream
  have regReadUnary : UnaryHistory regRead :=
    unary_cont_closed streamReadUnary tailUnary streamTailReg
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed regReadUnary toleranceUnary regToleranceDyadic
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicReadUnary sealRowUnary dyadicSealRead
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed sealReadUnary routesUnary sealRoutesReal
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed realReadUnary nameUnary realNameTerminal
  exact
    ⟨windowsUnary, modulusUnary, streamReadUnary, tailUnary, regReadUnary, toleranceUnary,
      dyadicReadUnary, sealRowUnary, sealReadUnary, routesUnary, realReadUnary,
      terminalUnary, windowsModulusStream, streamTailReg, regToleranceDyadic,
      dyadicSealRead, sealRoutesReal, realNameTerminal, namePkg, terminalPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
