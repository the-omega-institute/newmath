import BEDC.Derived.FanfunctionalUp.NameCertObligations

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FanFunctionalRootFiniteBarDepth [AskSetup] [PackageSetup]
    {cantor fan tolerance branch depth witness modulus transport replay provenance localName
      depthRead witnessRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanFunctionalCarrierSurface cantor fan tolerance branch depth witness modulus transport
        replay provenance localName bundle pkg ->
      Cont fan depth depthRead ->
        Cont depthRead witness witnessRead ->
          PkgSig bundle witnessRead pkg ->
            UnaryHistory depthRead ∧ UnaryHistory witnessRead ∧
              Cont fan depth depthRead ∧ Cont depthRead witness witnessRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle witnessRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier fanDepthRead depthWitnessRead witnessPkg
  obtain ⟨_cantorUnary, fanUnary, _toleranceUnary, _branchUnary, depthUnary, witnessUnary,
    _modulusUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _transportLocalName, _branchDepthWitness, _witnessModulusReplay, provenancePkg⟩ :=
    carrier
  have depthReadUnary : UnaryHistory depthRead :=
    unary_cont_closed fanUnary depthUnary fanDepthRead
  have witnessReadUnary : UnaryHistory witnessRead :=
    unary_cont_closed depthReadUnary witnessUnary depthWitnessRead
  exact
    ⟨depthReadUnary, witnessReadUnary, fanDepthRead, depthWitnessRead, provenancePkg,
      witnessPkg⟩

end BEDC.Derived.FanfunctionalUp
