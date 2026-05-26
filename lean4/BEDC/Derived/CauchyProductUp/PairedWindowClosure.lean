import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_paired_window_closure [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name windowClosure : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont windowA windowB transport ->
        Cont product ledger classifier ->
          Cont transport classifier windowClosure ->
            PkgSig bundle windowClosure pkg ->
              UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
                UnaryHistory windowB ∧ UnaryHistory product ∧ UnaryHistory classifier ∧
                  UnaryHistory windowClosure ∧ Cont windowA windowB transport ∧
                    Cont product ledger classifier ∧ Cont transport classifier windowClosure ∧
                      PkgSig bundle name pkg ∧ PkgSig bundle windowClosure pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet pairedWindow productClassifier transportClassifier closurePkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, _routesUnary, ledgerUnary,
    _packetPairedWindow, productRoute, _packetProductClassifier, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary productClassifier
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed windowAUnary windowBUnary pairedWindow
  have windowClosureUnary : UnaryHistory windowClosure :=
    unary_cont_closed transportUnary classifierUnary transportClassifier
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, productUnary, classifierUnary,
      windowClosureUnary, pairedWindow, productClassifier, transportClassifier, namePkg,
      closurePkg⟩

end BEDC.Derived.CauchyProductUp
