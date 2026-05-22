import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberRealCompletionTerminalRadiusExhaustion [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow terminalWindow terminalMesh
      terminalReal consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont window radius terminalWindow ->
        Cont terminalWindow mesh terminalMesh ->
          Cont terminalMesh route terminalReal ->
            Cont terminalReal nameRow consumerRead ->
              PkgSig bundle consumerRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row terminalWindow ∨ hsame row terminalMesh ∨
                        hsame row terminalReal ∨ hsame row consumerRead)
                    (fun row : BHist =>
                      PkgSig bundle consumerRead pkg ∧ hsame row consumerRead)
                    hsame ∧
                  UnaryHistory terminalWindow ∧ UnaryHistory terminalMesh ∧
                    UnaryHistory terminalReal ∧ UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier windowRadiusTerminal terminalMeshRoute terminalRealRoute
    realNameConsumer consumerPkg
  obtain ⟨_coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have terminalWindowUnary : UnaryHistory terminalWindow :=
    unary_cont_closed windowUnary radiusUnary windowRadiusTerminal
  have terminalMeshUnary : UnaryHistory terminalMesh :=
    unary_cont_closed terminalWindowUnary meshUnary terminalMeshRoute
  have terminalRealUnary : UnaryHistory terminalReal :=
    unary_cont_closed terminalMeshUnary routeUnary terminalRealRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed terminalRealUnary nameRowUnary realNameConsumer
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row terminalWindow ∨ hsame row terminalMesh ∨ hsame row terminalReal ∨
            hsame row consumerRead)
        (fun row : BHist => PkgSig bundle consumerRead pkg ∧ hsame row consumerRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerUnary⟩
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
        exact ⟨consumerPkg, source.left⟩
    }
  exact ⟨cert, terminalWindowUnary, terminalMeshUnary, terminalRealUnary, consumerUnary⟩

theorem FiniteLebesgueNumberTerminalRadiusChoiceRefusal [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow terminalRead compactRead
      compactNetRead continuousRead uniformRead refusedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont route nameRow terminalRead ->
        Cont terminalRead radius compactRead ->
          Cont compactRead mesh compactNetRead ->
            Cont compactNetRead route continuousRead ->
              Cont continuousRead nameRow uniformRead ->
                hsame refusedRead uniformRead ->
                  PkgSig bundle uniformRead pkg ->
                    UnaryHistory refusedRead ∧
                      SemanticNameCert
                        (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row refusedRead ∨ hsame row terminalRead ∨
                            hsame row compactRead ∨ hsame row compactNetRead ∨
                              hsame row continuousRead ∨ hsame row uniformRead)
                        (fun row : BHist =>
                          hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier routeNameTerminal terminalRadiusCompact compactMeshNet netRouteContinuous
    continuousNameUniform refusedUniform uniformPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
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
  have refusedUnary : UnaryHistory refusedRead :=
    unary_transport_symm uniformUnary refusedUniform
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row refusedRead ∨ hsame row terminalRead ∨
            hsame row compactRead ∨ hsame row compactNetRead ∨
              hsame row continuousRead ∨ hsame row uniformRead)
        (fun row : BHist => hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro uniformRead ⟨hsame_refl uniformRead, uniformUnary⟩
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
      exact Or.inl (hsame_trans source.left (hsame_symm refusedUniform))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, uniformPkg⟩
  }
  exact ⟨refusedUnary, cert⟩

end BEDC.Derived.FiniteLebesgueNumberUp
