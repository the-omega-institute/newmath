import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_real_tail_agreement_handoff [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name regseqSeal tailAgreement realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes regseqSeal ->
        Cont regseqSeal ledger tailAgreement ->
          Cont tailAgreement routes realSeal ->
            PkgSig bundle realSeal pkg ->
              UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory regseqSeal ∧
                UnaryHistory tailAgreement ∧ UnaryHistory realSeal ∧
                  Cont observationA observationB product ∧ Cont product ledger classifier ∧
                    Cont classifier routes regseqSeal ∧
                      Cont regseqSeal ledger tailAgreement ∧
                        Cont tailAgreement routes realSeal ∧ PkgSig bundle name pkg ∧
                          PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierRoutesRegseq regseqTailAgreement tailAgreementRealSeal realSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have regseqSealUnary : UnaryHistory regseqSeal :=
    unary_cont_closed classifierUnary routesUnary classifierRoutesRegseq
  have tailAgreementUnary : UnaryHistory tailAgreement :=
    unary_cont_closed regseqSealUnary ledgerUnary regseqTailAgreement
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed tailAgreementUnary routesUnary tailAgreementRealSeal
  exact
    ⟨productUnary, classifierUnary, regseqSealUnary, tailAgreementUnary, realSealUnary,
      productRoute, classifierRoute, classifierRoutesRegseq, regseqTailAgreement,
      tailAgreementRealSeal, namePkg, realSealPkg⟩

end BEDC.Derived.CauchyProductUp
