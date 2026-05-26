import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_paired_window_source_admission [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name pairedSource : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont sourceA sourceB pairedSource ->
        PkgSig bundle pairedSource pkg ->
          UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
            UnaryHistory windowB ∧ UnaryHistory pairedSource ∧
              Cont sourceA sourceB pairedSource ∧ Cont windowA windowB transport ∧
                PkgSig bundle name pkg ∧ PkgSig bundle pairedSource pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet sourcePair pairedPkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, _observationAUnary, _observationBUnary, _routesUnary, _ledgerUnary,
    windowTransport, _productRoute, _classifierRoute, namePkg⟩ := packet
  have pairedUnary : UnaryHistory pairedSource :=
    unary_cont_closed sourceAUnary sourceBUnary sourcePair
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, pairedUnary, sourcePair,
      windowTransport, namePkg, pairedPkg⟩

end BEDC.Derived.CauchyProductUp
