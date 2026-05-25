import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_ledger_obligation [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name ledgerSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont product routes ledgerSeal ->
        PkgSig bundle ledgerSeal pkg ->
          UnaryHistory radiusA ∧ UnaryHistory radiusB ∧ UnaryHistory observationA ∧
            UnaryHistory observationB ∧ UnaryHistory product ∧ UnaryHistory classifier ∧
              UnaryHistory transport ∧ UnaryHistory routes ∧ UnaryHistory ledger ∧
                UnaryHistory ledgerSeal ∧ Cont windowA windowB transport ∧
                  Cont observationA observationB product ∧ Cont product ledger classifier ∧
                    Cont product routes ledgerSeal ∧ PkgSig bundle name pkg ∧
                      PkgSig bundle ledgerSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet ledgerSealRoute ledgerSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, radiusAUnary,
    radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed windowAUnary windowBUnary windowTransport
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have ledgerSealUnary : UnaryHistory ledgerSeal :=
    unary_cont_closed productUnary routesUnary ledgerSealRoute
  exact
    ⟨radiusAUnary, radiusBUnary, observationAUnary, observationBUnary, productUnary,
      classifierUnary, transportUnary, routesUnary, ledgerUnary, ledgerSealUnary,
      windowTransport, productRoute, classifierRoute, ledgerSealRoute, namePkg,
      ledgerSealPkg⟩

end BEDC.Derived.CauchyProductUp
