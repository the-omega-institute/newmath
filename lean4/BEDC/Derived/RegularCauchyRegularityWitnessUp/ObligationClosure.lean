import BEDC.Derived.RegularCauchyRegularityWitnessUp.NameCertObligations

namespace BEDC.Derived.RegularCauchyRegularityWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyRegularityWitnessCarrier_obligation_closure [AskSetup]
    [PackageSetup] {S mu j Omega R Q E H C P N closureRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyRegularityWitnessCarrier S mu j Omega R Q E H C P N bundle pkg →
      Cont C N closureRead →
        PkgSig bundle closureRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row closureRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row S ∨ hsame row mu ∨ hsame row j ∨ hsame row Omega ∨
                  hsame row R ∨ hsame row Q ∨ hsame row E ∨ hsame row H ∨
                    hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row closureRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont S mu j ∧ Cont j Omega R ∧ Cont R Q E ∧
                  Cont E H C ∧ Cont C N closureRead ∧ PkgSig bundle closureRead pkg)
              hsame ∧
            UnaryHistory closureRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier closureRoute closurePkg
  obtain ⟨_unaryS, _unaryMu, _unaryJ, _unaryOmega, _unaryR, _unaryQ, _unaryE,
    _unaryH, cUnary, _unaryP, nUnary, routeSMuJ, routeJOmegaR, routeRQE,
    routeEHC, _pkgP, _pkgN⟩ := carrier
  have closureUnary : UnaryHistory closureRead :=
    unary_cont_closed cUnary nUnary closureRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row closureRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row mu ∨ hsame row j ∨ hsame row Omega ∨
              hsame row R ∨ hsame row Q ∨ hsame row E ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row closureRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S mu j ∧ Cont j Omega R ∧ Cont R Q E ∧
              Cont E H C ∧ Cont C N closureRead ∧ PkgSig bundle closureRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro closureRead ⟨hsame_refl closureRead, closureUnary⟩
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
      exact
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, routeSMuJ, routeJOmegaR, routeRQE, routeEHC, closureRoute,
          closurePkg⟩
  }
  exact ⟨cert, closureUnary⟩

end BEDC.Derived.RegularCauchyRegularityWitnessUp
