import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_streamname_regseqrat_real_window_lock
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name streamRead
      regseqRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont windows modulus streamRead ->
        Cont streamRead tolerance regseqRead ->
          Cont regseqRead sealRow realRead ->
            PkgSig bundle streamRead pkg ->
              PkgSig bundle regseqRead pkg ->
                PkgSig bundle realRead pkg ->
                  UnaryHistory windows ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
                    UnaryHistory sealRow ∧ UnaryHistory streamRead ∧
                      UnaryHistory regseqRead ∧ UnaryHistory realRead ∧
                        Cont windows modulus streamRead ∧
                          Cont streamRead tolerance regseqRead ∧
                            Cont regseqRead sealRow realRead ∧
                              PkgSig bundle streamRead pkg ∧
                                PkgSig bundle regseqRead pkg ∧
                                  PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet windowsModulusStream streamToleranceRegseq regseqSealReal streamPkg
    regseqPkg realPkg
  obtain ⟨_indexUnary, windowsUnary, modulusUnary, toleranceUnary, _tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, _namePkg⟩ := packet
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed windowsUnary modulusUnary windowsModulusStream
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed streamUnary toleranceUnary streamToleranceRegseq
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regseqUnary sealRowUnary regseqSealReal
  exact
    ⟨windowsUnary, modulusUnary, toleranceUnary, sealRowUnary, streamUnary, regseqUnary,
      realUnary, windowsModulusStream, streamToleranceRegseq, regseqSealReal, streamPkg,
      regseqPkg, realPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
