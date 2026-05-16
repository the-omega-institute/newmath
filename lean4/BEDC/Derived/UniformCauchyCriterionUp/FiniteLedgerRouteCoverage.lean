import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_finite_ledger_route_coverage [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name regseqRead
      realRead consumerRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail regseqRead ->
        Cont tail sealRow realRead ->
          Cont regseqRead realRead consumerRead ->
            Cont consumerRead provenance completionRead ->
              PkgSig bundle completionRead pkg ->
                UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
                  UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
                    UnaryHistory regseqRead ∧ UnaryHistory realRead ∧
                      UnaryHistory consumerRead ∧ UnaryHistory completionRead ∧
                        Cont index windows modulus ∧ Cont modulus tolerance tail ∧
                          Cont index tail regseqRead ∧ Cont tail sealRow realRead ∧
                            Cont regseqRead realRead consumerRead ∧
                              Cont consumerRead provenance completionRead ∧
                                PkgSig bundle name pkg ∧
                                  PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexTailRegseq tailSealReal regseqRealConsumer consumerProvenanceCompletion
    completionPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed indexUnary tailUnary indexTailRegseq
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealReal
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed regseqUnary realUnary regseqRealConsumer
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed consumerUnary provenanceUnary consumerProvenanceCompletion
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      regseqUnary, realUnary, consumerUnary, completionUnary, indexWindowsModulus,
      modulusToleranceTail, indexTailRegseq, tailSealReal, regseqRealConsumer,
      consumerProvenanceCompletion, namePkg, completionPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
