import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_shared_window_regseqrat_real_pullback
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name streamRead
      regseqRead realRead pullback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont windows modulus streamRead ->
        Cont streamRead tolerance regseqRead ->
          Cont regseqRead sealRow realRead ->
            Cont regseqRead realRead pullback ->
              PkgSig bundle streamRead pkg ->
                PkgSig bundle regseqRead pkg ->
                  PkgSig bundle realRead pkg ->
                    PkgSig bundle pullback pkg ->
                      UnaryHistory streamRead ∧ UnaryHistory regseqRead ∧
                        UnaryHistory realRead ∧ UnaryHistory pullback ∧
                          Cont windows modulus streamRead ∧
                            Cont streamRead tolerance regseqRead ∧
                              Cont regseqRead sealRow realRead ∧
                                Cont regseqRead realRead pullback ∧
                                  PkgSig bundle streamRead pkg ∧
                                    PkgSig bundle regseqRead pkg ∧
                                      PkgSig bundle realRead pkg ∧
                                        PkgSig bundle pullback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet windowsModulusStream streamToleranceRegseq regseqSealReal regseqRealPullback
    streamPkg regseqPkg realPkg pullbackPkg
  obtain ⟨_indexUnary, windowsUnary, modulusUnary, toleranceUnary, _tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, _namePkg⟩ :=
      packet
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed windowsUnary modulusUnary windowsModulusStream
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed streamUnary toleranceUnary streamToleranceRegseq
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regseqUnary sealRowUnary regseqSealReal
  have pullbackUnary : UnaryHistory pullback :=
    unary_cont_closed regseqUnary realUnary regseqRealPullback
  exact
    ⟨streamUnary, regseqUnary, realUnary, pullbackUnary, windowsModulusStream,
      streamToleranceRegseq, regseqSealReal, regseqRealPullback, streamPkg, regseqPkg,
      realPkg, pullbackPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
