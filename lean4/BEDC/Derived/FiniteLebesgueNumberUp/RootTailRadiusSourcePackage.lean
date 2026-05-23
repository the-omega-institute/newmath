import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberRootRadiusChoiceFreeTailExhaustion [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow tailRead realRead
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont radius mesh tailRead ->
        Cont tailRead route realRead ->
          Cont realRead nameRow consumerRead ->
            PkgSig bundle consumerRead pkg ->
              UnaryHistory tailRead ∧ UnaryHistory realRead ∧ UnaryHistory consumerRead ∧
                Cont radius mesh tailRead ∧ Cont tailRead route realRead ∧
                  Cont realRead nameRow consumerRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier radiusMeshTail tailRouteReal realNameConsumer consumerPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed radiusUnary meshUnary radiusMeshTail
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary routeUnary tailRouteReal
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed realUnary nameRowUnary realNameConsumer
  exact
    ⟨tailUnary, realUnary, consumerUnary, radiusMeshTail, tailRouteReal,
      realNameConsumer, provenancePkg, consumerPkg⟩

theorem FiniteLebesgueNumberRootRadiusNameCertObligationPackage [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow tailRead realRead sourceRead
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont route radius tailRead ->
        Cont tailRead window realRead ->
          Cont realRead nameRow sourceRead ->
            Cont sourceRead mesh consumerRead ->
              PkgSig bundle consumerRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row tailRead ∨ hsame row realRead ∨
                        hsame row sourceRead ∨ hsame row consumerRead)
                    (fun row : BHist =>
                      hsame row consumerRead ∧ PkgSig bundle consumerRead pkg)
                    hsame ∧
                  UnaryHistory tailRead ∧ UnaryHistory realRead ∧
                    UnaryHistory sourceRead ∧ UnaryHistory consumerRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier routeRadiusTail tailWindowReal realNameSource sourceMeshConsumer consumerPkg
  obtain ⟨_coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed routeUnary radiusUnary routeRadiusTail
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary windowUnary tailWindowReal
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed realUnary nameRowUnary realNameSource
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed sourceUnary meshUnary sourceMeshConsumer
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row tailRead ∨ hsame row realRead ∨
            hsame row sourceRead ∨ hsame row consumerRead)
        (fun row : BHist => hsame row consumerRead ∧ PkgSig bundle consumerRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerUnary⟩
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
      exact ⟨source.left, consumerPkg⟩
  }
  exact ⟨cert, tailUnary, realUnary, sourceUnary, consumerUnary, provenancePkg, consumerPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
