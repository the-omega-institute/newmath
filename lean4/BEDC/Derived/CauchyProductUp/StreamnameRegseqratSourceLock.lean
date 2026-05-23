import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_streamname_regseqrat_source_lock [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name regseqRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont transport routes regseqRead ->
        PkgSig bundle regseqRead pkg ->
          UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
            UnaryHistory windowB ∧ UnaryHistory transport ∧ UnaryHistory regseqRead ∧
              Cont windowA windowB transport ∧ Cont transport routes regseqRead ∧
                PkgSig bundle name pkg ∧ PkgSig bundle regseqRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet transportRoutesRegseqRead regseqReadPkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, _observationAUnary, _observationBUnary, routesUnary, _ledgerUnary,
    windowTransport, _productRoute, _classifierRoute, namePkg⟩ := packet
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed windowAUnary windowBUnary windowTransport
  have regseqReadUnary : UnaryHistory regseqRead :=
    unary_cont_closed transportUnary routesUnary transportRoutesRegseqRead
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, transportUnary,
      regseqReadUnary, windowTransport, transportRoutesRegseqRead, namePkg, regseqReadPkg⟩

end BEDC.Derived.CauchyProductUp
