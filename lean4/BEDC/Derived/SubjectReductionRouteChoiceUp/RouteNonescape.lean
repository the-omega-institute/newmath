import BEDC.Derived.SubjectReductionRouteChoiceUp.ObligationSurface

namespace BEDC.Derived.SubjectReductionRouteChoiceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SubjectReductionRouteChoiceCarrier_nonescape [AskSetup] [PackageSetup]
    {typedTerm sourceType targetType routeLeft routeRight subjectTrace reductionTrace
      substitutionTrace obstruction boundary continuation provenance name blockedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubjectReductionRouteChoiceCarrier typedTerm sourceType targetType routeLeft routeRight
        subjectTrace reductionTrace substitutionTrace obstruction boundary continuation provenance
        name bundle pkg →
      Cont routeLeft routeRight blockedRead →
        PkgSig bundle blockedRead pkg →
          UnaryHistory typedTerm ∧ UnaryHistory sourceType ∧ UnaryHistory targetType ∧
            UnaryHistory routeLeft ∧ UnaryHistory routeRight ∧ UnaryHistory blockedRead ∧
              Cont routeLeft routeRight blockedRead ∧ PkgSig bundle name pkg ∧
                PkgSig bundle blockedRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory ProbeBundle Pkg PkgSig
  intro carrier blockedRoute blockedPkg
  obtain ⟨typedUnary, sourceUnary, targetUnary, leftUnary, rightUnary, _transportUnary,
    _replayUnary, _substitutionUnary, _obstructionUnary, _boundaryUnary, _continuationUnary,
    _provenanceUnary, _nameUnary, _typedRoute, _targetRoute, _substitutionRoute,
    _continuationRoute, namePkg⟩ := carrier
  have blockedUnary : UnaryHistory blockedRead :=
    unary_cont_closed leftUnary rightUnary blockedRoute
  exact
    ⟨typedUnary, sourceUnary, targetUnary, leftUnary, rightUnary, blockedUnary,
      blockedRoute, namePkg, blockedPkg⟩

end BEDC.Derived.SubjectReductionRouteChoiceUp
