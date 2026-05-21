import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberChoiceFreeTailRadiusAdmission [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow tailAdmission streamTail
      regularTail realTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont window radius tailAdmission ->
        Cont tailAdmission mesh streamTail ->
          Cont streamTail route regularTail ->
            Cont regularTail nameRow realTail ->
              PkgSig bundle realTail pkg ->
                UnaryHistory window ∧ UnaryHistory radius ∧ UnaryHistory tailAdmission ∧
                  UnaryHistory streamTail ∧ UnaryHistory regularTail ∧ UnaryHistory realTail ∧
                    Cont window radius tailAdmission ∧ Cont tailAdmission mesh streamTail ∧
                      Cont streamTail route regularTail ∧ Cont regularTail nameRow realTail ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle realTail pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier windowRadiusTail tailMeshStream streamRouteRegular regularNameReal realPkg
  obtain ⟨_coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have tailUnary : UnaryHistory tailAdmission :=
    unary_cont_closed windowUnary radiusUnary windowRadiusTail
  have streamUnary : UnaryHistory streamTail :=
    unary_cont_closed tailUnary meshUnary tailMeshStream
  have regularUnary : UnaryHistory regularTail :=
    unary_cont_closed streamUnary routeUnary streamRouteRegular
  have realUnary : UnaryHistory realTail :=
    unary_cont_closed regularUnary nameRowUnary regularNameReal
  exact
    ⟨windowUnary, radiusUnary, tailUnary, streamUnary, regularUnary, realUnary,
      windowRadiusTail, tailMeshStream, streamRouteRegular, regularNameReal, provenancePkg,
      realPkg⟩

theorem FiniteLebesgueNumberCompactRadiusWindowPullback [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow compactRadius compactWindow
      pullbackRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont cover radius compactRadius ->
        Cont compactRadius mesh compactWindow ->
          Cont compactWindow route pullbackRead ->
            PkgSig bundle pullbackRead pkg ->
              UnaryHistory cover ∧ UnaryHistory radius ∧ UnaryHistory mesh ∧
                UnaryHistory compactRadius ∧ UnaryHistory compactWindow ∧
                  UnaryHistory pullbackRead ∧ Cont cover window radius ∧
                    Cont cover radius compactRadius ∧ Cont compactRadius mesh compactWindow ∧
                      Cont compactWindow route pullbackRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle pullbackRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier coverRadiusCompact compactMeshWindow windowRoutePullback pullbackPkg
  obtain ⟨coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameRowUnary, coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have compactRadiusUnary : UnaryHistory compactRadius :=
    unary_cont_closed coverUnary radiusUnary coverRadiusCompact
  have compactWindowUnary : UnaryHistory compactWindow :=
    unary_cont_closed compactRadiusUnary meshUnary compactMeshWindow
  have pullbackUnary : UnaryHistory pullbackRead :=
    unary_cont_closed compactWindowUnary routeUnary windowRoutePullback
  exact
    ⟨coverUnary, radiusUnary, meshUnary, compactRadiusUnary, compactWindowUnary,
      pullbackUnary, coverWindowRadius, coverRadiusCompact, compactMeshWindow,
      windowRoutePullback, provenancePkg, pullbackPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
