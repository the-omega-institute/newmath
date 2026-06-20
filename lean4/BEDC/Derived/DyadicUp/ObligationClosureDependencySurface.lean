import BEDC.Derived.DyadicUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DyadicUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicUp_obligation_closure_dependency_surface [AskSetup] [PackageSetup]
    {Q S R E H C P N routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCarrier Q S R E H C P N bundle pkg ->
      Cont Q S routeRead ->
        PkgSig bundle routeRead pkg ->
          SemanticNameCert
            (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row Q ∨ hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row routeRead)
            (fun row : BHist =>
              UnaryHistory row ∧ Cont Q S routeRead ∧ Cont Q S R ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                  PkgSig bundle routeRead pkg)
            hsame ∧ UnaryHistory routeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier routeCont routePkg
  obtain ⟨qUnary, sUnary, _rUnary, _eUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    qsrRoute, _recRoute, provenancePkg, namePkg⟩ := carrier
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed qUnary sUnary routeCont
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row Q ∨ hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
            hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row routeRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont Q S routeRead ∧ Cont Q S R ∧
            PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧ PkgSig bundle routeRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro routeRead ⟨hsame_refl routeRead, routeUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, routeCont, qsrRoute, provenancePkg, namePkg, routePkg⟩
  }
  exact ⟨cert, routeUnary⟩

end BEDC.Derived.DyadicUp
