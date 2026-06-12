import BEDC.Derived.FanfunctionalUp.NameCertObligations

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FanFunctionalRootBarDepthExactness [AskSetup] [PackageSetup]
    {cantor fan tolerance branch depth witness modulus transport replay provenance localName
      depthRead modulusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanFunctionalCarrierSurface cantor fan tolerance branch depth witness modulus transport replay
        provenance localName bundle pkg →
      Cont fan depth depthRead →
        Cont depthRead modulus modulusRead →
          PkgSig bundle modulusRead pkg →
            UnaryHistory fan ∧ UnaryHistory depth ∧ UnaryHistory depthRead ∧
              UnaryHistory modulus ∧ UnaryHistory modulusRead ∧ Cont fan depth depthRead ∧
                Cont depthRead modulus modulusRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle modulusRead pkg := by
  -- BEDC touchpoint anchor: FanFunctionalCarrierSurface BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier fanDepthRead depthReadModulusRead modulusReadPkg
  obtain ⟨_cantorUnary, fanUnary, _toleranceUnary, _branchUnary, depthUnary,
    _witnessUnary, modulusUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _transportLocalName, _branchDepthWitness, _witnessModulusReplay,
    provenancePkg⟩ := carrier
  have depthReadUnary : UnaryHistory depthRead :=
    unary_cont_closed fanUnary depthUnary fanDepthRead
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed depthReadUnary modulusUnary depthReadModulusRead
  exact
    ⟨fanUnary, depthUnary, depthReadUnary, modulusUnary, modulusReadUnary,
      fanDepthRead, depthReadModulusRead, provenancePkg, modulusReadPkg⟩

end BEDC.Derived.FanfunctionalUp
