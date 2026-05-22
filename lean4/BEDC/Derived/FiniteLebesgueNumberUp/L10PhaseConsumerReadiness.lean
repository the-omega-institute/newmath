import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberL10PhaseConsumerReadiness [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow rootRead phaseRead
      consumerRead terminalRead compactRead compactNetRead continuousRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont route nameRow rootRead ->
        Cont rootRead radius phaseRead ->
          Cont phaseRead mesh consumerRead ->
            Cont route nameRow terminalRead ->
              Cont terminalRead radius compactRead ->
                Cont compactRead mesh compactNetRead ->
                  Cont compactNetRead route continuousRead ->
                    Cont continuousRead nameRow uniformRead ->
                      PkgSig bundle uniformRead pkg ->
                        UnaryHistory rootRead ∧ UnaryHistory phaseRead ∧
                          UnaryHistory consumerRead ∧ UnaryHistory terminalRead ∧
                            UnaryHistory compactRead ∧ UnaryHistory compactNetRead ∧
                              UnaryHistory continuousRead ∧ UnaryHistory uniformRead ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier routeNameRoot rootRadiusPhase phaseMeshConsumer routeNameTerminal
    terminalRadiusCompact compactMeshNet netRouteContinuous continuousNameUniform uniformPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameRoot
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed rootUnary radiusUnary rootRadiusPhase
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed phaseUnary meshUnary phaseMeshConsumer
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameTerminal
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed terminalUnary radiusUnary terminalRadiusCompact
  have compactNetUnary : UnaryHistory compactNetRead :=
    unary_cont_closed compactUnary meshUnary compactMeshNet
  have continuousUnary : UnaryHistory continuousRead :=
    unary_cont_closed compactNetUnary routeUnary netRouteContinuous
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed continuousUnary nameRowUnary continuousNameUniform
  exact
    ⟨rootUnary, phaseUnary, consumerUnary, terminalUnary, compactUnary, compactNetUnary,
      continuousUnary, uniformUnary, provenancePkg, uniformPkg⟩

theorem FiniteLebesgueNumberL10ConsumerReadbackExactness [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow rootRead phaseRead sourceRead
      regularRead realRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont route nameRow rootRead ->
        Cont rootRead radius phaseRead ->
          Cont phaseRead mesh sourceRead ->
            Cont sourceRead route regularRead ->
              Cont regularRead nameRow realRead ->
                Cont realRead radius consumerRead ->
                  PkgSig bundle consumerRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row sourceRead ∨ hsame row regularRead ∨
                            hsame row realRead ∨ hsame row consumerRead)
                        (fun row : BHist =>
                          PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg ∧
                            hsame row consumerRead)
                        hsame ∧
                      UnaryHistory sourceRead ∧ UnaryHistory regularRead ∧
                        UnaryHistory realRead ∧ UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier routeNameRoot rootRadiusPhase phaseMeshSource sourceRouteRegular
    regularNameReal realRadiusConsumer consumerPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameRoot
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed rootUnary radiusUnary rootRadiusPhase
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed phaseUnary meshUnary phaseMeshSource
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed sourceUnary routeUnary sourceRouteRegular
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regularUnary nameRowUnary regularNameReal
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed realUnary radiusUnary realRadiusConsumer
  have sourceConsumer :
      (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row) consumerRead := by
    exact ⟨hsame_refl consumerRead, consumerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sourceRead ∨ hsame row regularRead ∨ hsame row realRead ∨
              hsame row consumerRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg ∧
              hsame row consumerRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro consumerRead sourceConsumer
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, consumerPkg, source.left⟩
    }
  exact ⟨cert, sourceUnary, regularUnary, realUnary, consumerUnary⟩

end BEDC.Derived.FiniteLebesgueNumberUp
