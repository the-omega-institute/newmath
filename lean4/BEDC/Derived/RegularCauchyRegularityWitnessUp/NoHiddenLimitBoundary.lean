import BEDC.Derived.RegularCauchyRegularityWitnessUp.NameCertObligations

namespace BEDC.Derived.RegularCauchyRegularityWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyRegularityWitness_no_hidden_limit_boundary [AskSetup] [PackageSetup]
    {S mu j Omega R Q E H C P N hiddenRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyRegularityWitnessCarrier S mu j Omega R Q E H C P N bundle pkg →
      Cont E H hiddenRead →
        PkgSig bundle hiddenRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row hiddenRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row S ∨ hsame row Omega ∨ hsame row R ∨ hsame row Q ∨
                  hsame row E ∨ hsame row hiddenRead)
              (fun row : BHist => hsame row hiddenRead ∧ PkgSig bundle hiddenRead pkg)
              hsame ∧
            UnaryHistory hiddenRead ∧ PkgSig bundle hiddenRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier hiddenRoute hiddenPkg
  obtain ⟨_sUnary, _muUnary, _jUnary, _omegaUnary, _rUnary, _qUnary, eUnary, hUnary,
    _cUnary, _pUnary, _nUnary, _routeSMuJ, _routeJOmegaR, _routeRQE, _routeEHC,
    _pkgP, _pkgN⟩ := carrier
  have hiddenUnary : UnaryHistory hiddenRead :=
    unary_cont_closed eUnary hUnary hiddenRoute
  have sourceAtHidden : hsame hiddenRead hiddenRead ∧ UnaryHistory hiddenRead :=
    ⟨hsame_refl hiddenRead, hiddenUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row hiddenRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row Omega ∨ hsame row R ∨ hsame row Q ∨
              hsame row E ∨ hsame row hiddenRead)
          (fun row : BHist => hsame row hiddenRead ∧ PkgSig bundle hiddenRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro hiddenRead sourceAtHidden
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, hiddenPkg⟩
  }
  exact ⟨cert, hiddenUnary, hiddenPkg⟩

end BEDC.Derived.RegularCauchyRegularityWitnessUp
