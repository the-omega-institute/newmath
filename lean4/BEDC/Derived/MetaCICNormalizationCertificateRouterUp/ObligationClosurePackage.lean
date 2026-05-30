import BEDC.Derived.MetaCICNormalizationCertificateRouterUp.TasteGate

namespace BEDC.Derived.MetaCICNormalizationCertificateRouterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationCertificateRouterObligationClosurePackage [AskSetup]
    [PackageSetup]
    {audit candidate strongNorm piApp closedProjection generator compiler kernelAccept transport
      replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationCertificateRouterCarrier audit candidate strongNorm piApp
        closedProjection generator compiler kernelAccept transport replay provenance localName
        bundle pkg →
      ∃ packageRead : BHist,
        UnaryHistory audit ∧ UnaryHistory candidate ∧ UnaryHistory strongNorm ∧
          UnaryHistory piApp ∧ UnaryHistory closedProjection ∧ UnaryHistory generator ∧
            UnaryHistory compiler ∧ UnaryHistory kernelAccept ∧ UnaryHistory packageRead ∧
              hsame packageRead (append audit candidate) ∧ Cont candidate strongNorm piApp ∧
                Cont piApp closedProjection transport ∧ Cont generator compiler kernelAccept ∧
                  Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame append
  intro carrier
  obtain ⟨auditUnary, candidateUnary, strongNormUnary, piAppUnary, closedProjectionUnary,
    generatorUnary, compilerUnary, kernelAcceptUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, candidateStrongNorm, piAppProjection,
    generatorCompiler, transportReplay, provenancePkg, localNamePkg⟩ := carrier
  refine ⟨append audit candidate, ?_⟩
  have packageReadUnary : UnaryHistory (append audit candidate) :=
    unary_append_closed auditUnary candidateUnary
  exact
    ⟨auditUnary, candidateUnary, strongNormUnary, piAppUnary, closedProjectionUnary,
      generatorUnary, compilerUnary, kernelAcceptUnary, packageReadUnary, hsame_refl _,
      candidateStrongNorm, piAppProjection, generatorCompiler, transportReplay, provenancePkg,
      localNamePkg⟩

end BEDC.Derived.MetaCICNormalizationCertificateRouterUp
