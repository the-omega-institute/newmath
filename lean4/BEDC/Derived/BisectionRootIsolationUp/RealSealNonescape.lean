import BEDC.Derived.BisectionRootIsolationUp.RegSeqRatWindowHandoff

namespace BEDC.Derived.BisectionRootIsolationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BisectionRootIsolationRealSealNonescape [AskSetup] [PackageSetup]
    {interval bisection functionRow endpoint window readback sealRow transport replay provenance name
      realRead exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BisectionRootIsolationCarrier interval bisection functionRow endpoint window readback sealRow
        transport replay provenance name bundle pkg ->
      Cont readback sealRow realRead ->
        Cont realRead replay exported ->
          PkgSig bundle exported pkg ->
            UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory realRead ∧
              UnaryHistory exported ∧ Cont readback sealRow realRead ∧
                Cont realRead replay exported ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle exported pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier realRoute exportRoute exportedPkg
  obtain ⟨_intervalUnary, _bisectionUnary, _functionUnary, _endpointUnary, _windowUnary,
    readbackUnary, sealUnary, _transportUnary, replayUnary, _provenanceUnary, _nameUnary,
    _sealRoute, _endpointRoute, provenancePkg⟩ := carrier
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed readbackUnary sealUnary realRoute
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed realReadUnary replayUnary exportRoute
  exact
    ⟨readbackUnary, sealUnary, realReadUnary, exportedUnary, realRoute, exportRoute,
      provenancePkg, exportedPkg⟩

end BEDC.Derived.BisectionRootIsolationUp
