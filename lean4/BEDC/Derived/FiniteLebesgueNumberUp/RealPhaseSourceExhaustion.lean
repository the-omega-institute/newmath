import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberRealPhaseOfftableRefusal [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow realRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont route nameRow realRead ->
        Cont realRead radius consumerRead ->
          PkgSig bundle consumerRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row realRead ∨ hsame row radius ∨ hsame row consumerRead)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg ∧
                    hsame row consumerRead)
                hsame ∧
              UnaryHistory realRead ∧ UnaryHistory consumerRead ∧ Cont route nameRow realRead ∧
                Cont realRead radius consumerRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier routeNameReal realRadiusConsumer consumerPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, _meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameReal
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed realUnary radiusUnary realRadiusConsumer
  have sourceConsumer :
      (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row) consumerRead := by
    exact ⟨hsame_refl consumerRead, consumerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row realRead ∨ hsame row radius ∨ hsame row consumerRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg ∧
              hsame row consumerRead)
          hsame := {
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, consumerPkg, source.left⟩
  }
  exact
    ⟨cert, realUnary, consumerUnary, routeNameReal, realRadiusConsumer, provenancePkg,
      consumerPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
