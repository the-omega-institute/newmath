import BEDC.Derived.BoundedSetUp.BallContainmentRoute

namespace BEDC.Derived.BoundedSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedSetCarrier_obligation_classifier_transport [AskSetup] [PackageSetup]
    {X S center radius ball transport replay provenance nameRow memberRead classifierRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedSetCarrier X S center radius ball transport replay provenance nameRow bundle pkg ->
      Cont S center memberRead ->
        Cont memberRead transport classifierRead ->
          PkgSig bundle classifierRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row S ∨ hsame row center ∨ hsame row transport ∨
                    hsame row classifierRead ∨ Cont S center memberRead ∨
                      Cont memberRead transport classifierRead)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle classifierRead pkg ∧
                    hsame row classifierRead)
                hsame ∧
              UnaryHistory memberRead ∧ UnaryHistory classifierRead ∧
                Cont S center memberRead ∧ Cont memberRead transport classifierRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle classifierRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro carrier memberRoute classifierRoute classifierPkg
  obtain ⟨_xUnary, sUnary, centerUnary, _radiusUnary, _ballUnary, transportUnary,
    _replayUnary, _provenanceUnary, _nameUnary, _carrierMemberRoute, _carrierBallRoute,
    provenancePkg, _namePkg⟩ := carrier
  have memberUnary : UnaryHistory memberRead :=
    unary_cont_closed sUnary centerUnary memberRoute
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed memberUnary transportUnary classifierRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row center ∨ hsame row transport ∨
              hsame row classifierRead ∨ Cont S center memberRead ∨
                Cont memberRead transport classifierRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle classifierRead pkg ∧
              hsame row classifierRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro classifierRead
        ⟨hsame_refl classifierRead, classifierUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, classifierPkg, source.left⟩
  }
  exact
    ⟨cert, memberUnary, classifierUnary, memberRoute, classifierRoute, provenancePkg,
      classifierPkg⟩

end BEDC.Derived.BoundedSetUp
