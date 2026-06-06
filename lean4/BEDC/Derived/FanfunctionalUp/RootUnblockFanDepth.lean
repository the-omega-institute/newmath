import BEDC.Derived.FanfunctionalUp.NameCertObligations

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FanFunctionalRootUnblockFanDepth [AskSetup] [PackageSetup]
    {cantor fan tolerance branch depth witness modulus transport replay provenance localName
      barRead fanDepthRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanFunctionalCarrierSurface cantor fan tolerance branch depth witness modulus transport replay
        provenance localName bundle pkg ->
      Cont branch depth barRead ->
        Cont barRead fan fanDepthRead ->
          PkgSig bundle fanDepthRead pkg ->
            UnaryHistory branch ∧ UnaryHistory depth ∧ UnaryHistory barRead ∧
              UnaryHistory fanDepthRead ∧ Cont branch depth barRead ∧
                Cont barRead fan fanDepthRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle fanDepthRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier branchDepthBar barFanDepth fanDepthPkg
  obtain ⟨_cantorUnary, fanUnary, _toleranceUnary, branchUnary, depthUnary, _witnessUnary,
    _modulusUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _transportLocalName, _branchDepthWitness, _witnessModulusReplay, provenancePkg⟩ :=
    carrier
  have barReadUnary : UnaryHistory barRead :=
    unary_cont_closed branchUnary depthUnary branchDepthBar
  have fanDepthReadUnary : UnaryHistory fanDepthRead :=
    unary_cont_closed barReadUnary fanUnary barFanDepth
  exact
    ⟨branchUnary, depthUnary, barReadUnary, fanDepthReadUnary, branchDepthBar, barFanDepth,
      provenancePkg, fanDepthPkg⟩

end BEDC.Derived.FanfunctionalUp
