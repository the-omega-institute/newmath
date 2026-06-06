import BEDC.Derived.PolishspaceUp.CompletionDensityHandoff

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceStreamReadbackExactness [AskSetup] [PackageSetup]
    {M K D S R W H C G N streamRead cauchyRead observationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.PolishSpaceUp.PolishSpaceCarrier M K D S R W H C G N bundle pkg ->
      Cont S R streamRead ->
        Cont streamRead W cauchyRead ->
          Cont cauchyRead M observationRead ->
            PkgSig bundle observationRead pkg ->
              UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory W ∧
                UnaryHistory streamRead ∧ UnaryHistory cauchyRead ∧
                  UnaryHistory observationRead ∧ Cont S R streamRead ∧
                    Cont streamRead W cauchyRead ∧ Cont cauchyRead M observationRead ∧
                      PkgSig bundle G pkg ∧ PkgSig bundle observationRead pkg := by
  -- BEDC touchpoint anchor: PolishSpaceCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier streamRoute cauchyRoute observationRoute observationPkg
  obtain ⟨MUnary, _KUnary, _DUnary, SUnary, RUnary, WUnary, _HUnary, _CUnary,
    _GUnary, _NUnary, _metricCompleteLedger, _ledgerStreamReadback,
    _transportReplayProvenance, provenancePkg, _localPkg⟩ := carrier
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed SUnary RUnary streamRoute
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed streamUnary WUnary cauchyRoute
  have observationUnary : UnaryHistory observationRead :=
    unary_cont_closed cauchyUnary MUnary observationRoute
  exact
    ⟨SUnary, RUnary, WUnary, streamUnary, cauchyUnary, observationUnary, streamRoute,
      cauchyRoute, observationRoute, provenancePkg, observationPkg⟩

end BEDC.Derived.PolishspaceUp
