import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

def FiniteLebesgueNumberCompactRadiusWindowPullbackPacket [AskSetup] [PackageSetup]
    (cover window radius mesh transport route provenance nameRow compactRadius compactWindow
      pullbackRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
      bundle pkg ∧
    Cont cover radius compactRadius ∧ Cont compactRadius mesh compactWindow ∧
      Cont compactWindow route pullbackRead ∧ PkgSig bundle pullbackRead pkg

theorem FiniteLebesgueNumberCompactRadiusWindowPullbackPacket_admission
    [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow compactRadius compactWindow
      pullbackRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCompactRadiusWindowPullbackPacket cover window radius mesh transport
        route provenance nameRow compactRadius compactWindow pullbackRead bundle pkg →
      UnaryHistory cover ∧ UnaryHistory radius ∧ UnaryHistory mesh ∧
        UnaryHistory compactRadius ∧ UnaryHistory compactWindow ∧
          UnaryHistory pullbackRead ∧ Cont cover radius compactRadius ∧
            Cont compactRadius mesh compactWindow ∧ Cont compactWindow route pullbackRead ∧
              PkgSig bundle pullbackRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet
  obtain ⟨carrier, coverRadiusCompact, compactMeshWindow, windowRoutePullback,
    pullbackPkg⟩ := packet
  obtain ⟨coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have compactRadiusUnary : UnaryHistory compactRadius :=
    unary_cont_closed coverUnary radiusUnary coverRadiusCompact
  have compactWindowUnary : UnaryHistory compactWindow :=
    unary_cont_closed compactRadiusUnary meshUnary compactMeshWindow
  have pullbackUnary : UnaryHistory pullbackRead :=
    unary_cont_closed compactWindowUnary routeUnary windowRoutePullback
  exact
    ⟨coverUnary, radiusUnary, meshUnary, compactRadiusUnary, compactWindowUnary,
      pullbackUnary, coverRadiusCompact, compactMeshWindow, windowRoutePullback,
      pullbackPkg⟩

theorem FiniteLebesgueNumberBudgetedRealCompletionNonescape [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow compactRadius compactWindow
      uniformRead realCompletionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont cover radius compactRadius →
        Cont compactRadius mesh compactWindow →
          Cont compactWindow route uniformRead →
            Cont uniformRead nameRow realCompletionRead →
              PkgSig bundle realCompletionRead pkg →
                UnaryHistory compactRadius ∧ UnaryHistory compactWindow ∧
                  UnaryHistory uniformRead ∧ UnaryHistory realCompletionRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle realCompletionRead pkg ∧
                      SemanticNameCert
                        (fun row : BHist => hsame row realCompletionRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row radius ∨ hsame row compactRadius ∨
                            hsame row compactWindow ∨ hsame row uniformRead ∨
                              hsame row realCompletionRead)
                        (fun row : BHist =>
                          hsame row realCompletionRead ∧
                            PkgSig bundle realCompletionRead pkg)
                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier coverRadiusCompact compactMeshWindow compactRouteUniform
    uniformNameCompletion completionPkg
  obtain ⟨coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have compactRadiusUnary : UnaryHistory compactRadius :=
    unary_cont_closed coverUnary radiusUnary coverRadiusCompact
  have compactWindowUnary : UnaryHistory compactWindow :=
    unary_cont_closed compactRadiusUnary meshUnary compactMeshWindow
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed compactWindowUnary routeUnary compactRouteUniform
  have completionUnary : UnaryHistory realCompletionRead :=
    unary_cont_closed uniformUnary nameRowUnary uniformNameCompletion
  have sourceCompletion :
      (fun row : BHist => hsame row realCompletionRead ∧ UnaryHistory row)
        realCompletionRead := by
    exact ⟨hsame_refl realCompletionRead, completionUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row realCompletionRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row radius ∨ hsame row compactRadius ∨ hsame row compactWindow ∨
            hsame row uniformRead ∨ hsame row realCompletionRead)
        (fun row : BHist =>
          hsame row realCompletionRead ∧ PkgSig bundle realCompletionRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro realCompletionRead sourceCompletion
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, completionPkg⟩
    }
  exact
    ⟨compactRadiusUnary, compactWindowUnary, uniformUnary, completionUnary, provenancePkg,
      completionPkg, cert⟩

theorem FiniteLebesgueNumberUniformModulusConsumerPullback [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow compactRadius compactWindow
      uniformRead realCompletionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont cover radius compactRadius ->
        Cont compactRadius mesh compactWindow ->
          Cont compactWindow route uniformRead ->
            Cont uniformRead nameRow realCompletionRead ->
              PkgSig bundle uniformRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row radius ∨ hsame row compactRadius ∨
                        hsame row compactWindow ∨ hsame row uniformRead)
                    (fun row : BHist =>
                      hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
                    hsame ∧
                  UnaryHistory compactRadius ∧ UnaryHistory compactWindow ∧
                    UnaryHistory uniformRead ∧ Cont cover radius compactRadius ∧
                      Cont compactRadius mesh compactWindow ∧
                        Cont compactWindow route uniformRead ∧
                          PkgSig bundle provenance pkg ∧
                            PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier coverRadiusCompact compactMeshWindow compactRouteUniform
    _uniformNameCompletion uniformPkg
  obtain ⟨coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have compactRadiusUnary : UnaryHistory compactRadius :=
    unary_cont_closed coverUnary radiusUnary coverRadiusCompact
  have compactWindowUnary : UnaryHistory compactWindow :=
    unary_cont_closed compactRadiusUnary meshUnary compactMeshWindow
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed compactWindowUnary routeUnary compactRouteUniform
  have sourceUniform :
      (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row) uniformRead := by
    exact ⟨hsame_refl uniformRead, uniformUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row radius ∨ hsame row compactRadius ∨ hsame row compactWindow ∨
            hsame row uniformRead)
        (fun row : BHist => hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro uniformRead sourceUniform
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, uniformPkg⟩
    }
  exact
    ⟨cert, compactRadiusUnary, compactWindowUnary, uniformUnary, coverRadiusCompact,
      compactMeshWindow, compactRouteUniform, provenancePkg, uniformPkg⟩

def FiniteLebesgueNumberChoiceFreeTailRadiusLedger [AskSetup] [PackageSetup]
    (cover window radius mesh tailAdmission streamTail regularTail realTail transport route
      provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
      bundle pkg ∧
    Cont window radius tailAdmission ∧
      Cont tailAdmission mesh streamTail ∧
        Cont streamTail route regularTail ∧
          Cont regularTail nameRow realTail ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle realTail pkg

theorem FiniteLebesgueNumberChoiceFreeTailRadiusLedger_fields [AskSetup] [PackageSetup]
    {cover window radius mesh tailAdmission streamTail regularTail realTail transport route
      provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberChoiceFreeTailRadiusLedger cover window radius mesh tailAdmission
        streamTail regularTail realTail transport route provenance nameRow bundle pkg ->
      UnaryHistory tailAdmission ∧ UnaryHistory streamTail ∧ UnaryHistory regularTail ∧
        UnaryHistory realTail ∧ Cont window radius tailAdmission ∧
          Cont tailAdmission mesh streamTail ∧ Cont streamTail route regularTail ∧
            Cont regularTail nameRow realTail ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle realTail pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro ledger
  obtain ⟨carrier, windowRadiusTail, tailMeshStream, streamRouteRegular, regularNameReal,
    provenancePkg, realPkg⟩ := ledger
  obtain ⟨_coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _carrierPkg⟩ := carrier
  have tailUnary : UnaryHistory tailAdmission :=
    unary_cont_closed windowUnary radiusUnary windowRadiusTail
  have streamUnary : UnaryHistory streamTail :=
    unary_cont_closed tailUnary meshUnary tailMeshStream
  have regularUnary : UnaryHistory regularTail :=
    unary_cont_closed streamUnary routeUnary streamRouteRegular
  have realUnary : UnaryHistory realTail :=
    unary_cont_closed regularUnary nameRowUnary regularNameReal
  exact
    ⟨tailUnary, streamUnary, regularUnary, realUnary, windowRadiusTail, tailMeshStream,
      streamRouteRegular, regularNameReal, provenancePkg, realPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
