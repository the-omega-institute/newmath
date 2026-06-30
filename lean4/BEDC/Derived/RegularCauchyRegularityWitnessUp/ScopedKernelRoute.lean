import BEDC.Derived.RegularCauchyRegularityWitnessUp.NameCertObligations
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyRegularityWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyRegularityWitness_scoped_kernel_route [AskSetup] [PackageSetup]
    {S mu j Omega R Q E H C P N scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyRegularityWitnessCarrier S mu j Omega R Q E H C P N bundle pkg →
      Cont E H scopedRead →
        PkgSig bundle scopedRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row S ∨ hsame row Omega ∨ hsame row R ∨ hsame row Q ∨
                  hsame row E ∨ hsame row scopedRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont S mu j ∧ Cont j Omega R ∧ Cont R Q E ∧
                  Cont E H C ∧ PkgSig bundle scopedRead pkg)
              hsame ∧
            UnaryHistory scopedRead ∧ Cont S mu j ∧ Cont j Omega R ∧ Cont R Q E ∧
              Cont E H C ∧ PkgSig bundle scopedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier scopedRoute scopedPkg
  obtain ⟨_unaryS, _unaryMu, _unaryJ, _unaryOmega, _unaryR, _unaryQ, unaryE,
    unaryH, _unaryC, _unaryP, _unaryN, routeSMuJ, routeJOmegaR, routeRQE,
    routeEHC, _pkgP, _pkgN⟩ := carrier
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed unaryE unaryH scopedRoute
  have sourceScoped :
      (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row) scopedRead := by
    exact ⟨hsame_refl scopedRead, scopedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row Omega ∨ hsame row R ∨ hsame row Q ∨
              hsame row E ∨ hsame row scopedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S mu j ∧ Cont j Omega R ∧ Cont R Q E ∧
              Cont E H C ∧ PkgSig bundle scopedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopedRead sourceScoped
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
        exact ⟨hsame_trans (hsame_symm same) source.left, unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, routeSMuJ, routeJOmegaR, routeRQE, routeEHC, scopedPkg⟩
  }
  exact ⟨cert, scopedUnary, routeSMuJ, routeJOmegaR, routeRQE, routeEHC, scopedPkg⟩

end BEDC.Derived.RegularCauchyRegularityWitnessUp
