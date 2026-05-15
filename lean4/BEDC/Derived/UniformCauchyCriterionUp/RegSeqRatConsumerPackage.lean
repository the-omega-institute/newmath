import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_regseqrat_consumer_package [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name regseqRead
      realRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail regseqRead ->
        Cont tail sealRow realRead ->
          Cont regseqRead realRead consumerRead ->
            PkgSig bundle regseqRead pkg ->
              PkgSig bundle realRead pkg ->
                PkgSig bundle consumerRead pkg ->
                  UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
                    UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
                      UnaryHistory regseqRead ∧ UnaryHistory realRead ∧
                        UnaryHistory consumerRead ∧ Cont index windows modulus ∧
                          Cont modulus tolerance tail ∧ Cont index tail regseqRead ∧
                            Cont tail sealRow realRead ∧
                              Cont regseqRead realRead consumerRead ∧
                                PkgSig bundle name pkg ∧ PkgSig bundle regseqRead pkg ∧
                                  PkgSig bundle realRead pkg ∧
                                    PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexTailRegseq tailSealReal regseqRealConsumer regseqPkg realPkg
    consumerPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed indexUnary tailUnary indexTailRegseq
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealReal
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed regseqUnary realUnary regseqRealConsumer
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      regseqUnary, realUnary, consumerUnary, indexWindowsModulus, modulusToleranceTail,
      indexTailRegseq, tailSealReal, regseqRealConsumer, namePkg, regseqPkg, realPkg,
      consumerPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
