import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_streamname_handoff [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name streamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont transport routes streamRead ->
        PkgSig bundle streamRead pkg ->
          UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory transport ∧
            UnaryHistory streamRead ∧ Cont windowA windowB transport ∧
              Cont transport routes streamRead ∧ PkgSig bundle name pkg ∧
                PkgSig bundle streamRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet transportRoutesStreamRead streamReadPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, _observationAUnary, _observationBUnary, routesUnary, _ledgerUnary,
    windowTransport, _productRoute, _classifierRoute, namePkg⟩ := packet
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed windowAUnary windowBUnary windowTransport
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed transportUnary routesUnary transportRoutesStreamRead
  exact
    ⟨windowAUnary, windowBUnary, transportUnary, streamReadUnary, windowTransport,
      transportRoutesStreamRead, namePkg, streamReadPkg⟩

theorem CauchyProductPacket_source_window_tail_agreement_exhaustion [AskSetup]
    [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name streamRead regseqRead tailAgreementRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont transport routes streamRead ->
        Cont classifier routes regseqRead ->
          Cont regseqRead ledger tailAgreementRead ->
            PkgSig bundle tailAgreementRead pkg ->
              UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory transport ∧
                UnaryHistory streamRead ∧ UnaryHistory product ∧ UnaryHistory classifier ∧
                  UnaryHistory regseqRead ∧ UnaryHistory tailAgreementRead ∧
                    Cont windowA windowB transport ∧ Cont transport routes streamRead ∧
                      Cont observationA observationB product ∧ Cont product ledger classifier ∧
                        Cont classifier routes regseqRead ∧
                          Cont regseqRead ledger tailAgreementRead ∧ PkgSig bundle name pkg ∧
                            PkgSig bundle tailAgreementRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet transportRoutesStreamRead classifierRegseqRead regseqTailAgreement
    tailAgreementPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed windowAUnary windowBUnary windowTransport
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed transportUnary routesUnary transportRoutesStreamRead
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have regseqReadUnary : UnaryHistory regseqRead :=
    unary_cont_closed classifierUnary routesUnary classifierRegseqRead
  have tailAgreementReadUnary : UnaryHistory tailAgreementRead :=
    unary_cont_closed regseqReadUnary ledgerUnary regseqTailAgreement
  exact
    ⟨windowAUnary, windowBUnary, transportUnary, streamReadUnary, productUnary,
      classifierUnary, regseqReadUnary, tailAgreementReadUnary, windowTransport,
      transportRoutesStreamRead, productRoute, classifierRoute, classifierRegseqRead,
      regseqTailAgreement, namePkg, tailAgreementPkg⟩

end BEDC.Derived.CauchyProductUp
