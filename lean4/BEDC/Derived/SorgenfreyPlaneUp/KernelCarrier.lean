import BEDC.Derived.SorgenfreyPlaneUp

namespace BEDC.Derived.SorgenfreyPlaneUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SorgenfreyPlaneNameCertObligations [AskSetup] [PackageSetup]
    {LX LY Q OX OY B S H C R N observableRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SorgenfreyPlaneCarrier LX LY Q OX OY B S H C R N bundle pkg →
      Cont B S observableRead →
        PkgSig bundle observableRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row N ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row LX ∨ hsame row LY ∨ hsame row Q ∨ hsame row OX ∨
                  hsame row OY ∨ hsame row B ∨ hsame row S ∨ hsame row observableRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont B S observableRead ∧
                  PkgSig bundle observableRead pkg)
              hsame ∧ UnaryHistory observableRead := by
  -- BEDC touchpoint anchor: SorgenfreyPlaneCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier observableRoute observablePkg
  obtain ⟨_lxUnary, _lyUnary, _qUnary, _oxUnary, _oyUnary, basisUnary, observableUnary,
    _transportUnary, _routeUnary, _provenanceUnary, nameUnary, _lowerLimitProduct,
    _componentRectangle, _observableRoute, _provenancePkg, _namePkg,
    nameObservable⟩ := carrier
  have observableReadUnary : UnaryHistory observableRead :=
    unary_cont_closed basisUnary observableUnary observableRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row LX ∨ hsame row LY ∨ hsame row Q ∨ hsame row OX ∨
              hsame row OY ∨ hsame row B ∨ hsame row S ∨ hsame row observableRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B S observableRead ∧ PkgSig bundle observableRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N ⟨hsame_refl N, nameUnary⟩
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
      right
      right
      right
      right
      right
      right
      exact Or.inl (hsame_trans source.left nameObservable)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, observableRoute, observablePkg⟩
  }
  exact ⟨cert, observableReadUnary⟩

end BEDC.Derived.SorgenfreyPlaneUp
