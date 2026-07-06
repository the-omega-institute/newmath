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

theorem DyadicUp_obligation_closure_scope [AskSetup] [PackageSetup]
    {Q S R E H C P N routeRead sealRead tailRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicCarrier Q S R E H C P N bundle pkg ->
      Cont Q S routeRead ->
        Cont R E sealRead ->
          Cont routeRead sealRead tailRead ->
            PkgSig bundle routeRead pkg ->
              PkgSig bundle sealRead pkg ->
                PkgSig bundle tailRead pkg ->
                  SemanticNameCert
                    (fun row : BHist => hsame row tailRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row Q ∨ hsame row S ∨ hsame row R ∨ hsame row E ∨
                        hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                          hsame row routeRead ∨ hsame row sealRead ∨ hsame row tailRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont Q S routeRead ∧ Cont R E sealRead ∧
                        Cont routeRead sealRead tailRead ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle N pkg ∧ PkgSig bundle routeRead pkg ∧
                            PkgSig bundle sealRead pkg ∧ PkgSig bundle tailRead pkg)
                    hsame ∧
                    UnaryHistory routeRead ∧ UnaryHistory sealRead ∧ UnaryHistory tailRead := by
  -- BEDC touchpoint anchor: DyadicCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier routeCont sealCont tailCont routePkg sealPkg tailPkg
  obtain ⟨qUnary, sUnary, rUnary, eUnary, _hUnary, _cUnary, pUnary, nUnary,
    _qsrRoute, _recRoute, provenancePkg, namePkg⟩ := carrier
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed qUnary sUnary routeCont
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed rUnary eUnary sealCont
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed routeUnary sealUnary tailCont
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row tailRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row Q ∨ hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
            hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row routeRead ∨
              hsame row sealRead ∨ hsame row tailRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont Q S routeRead ∧ Cont R E sealRead ∧
            Cont routeRead sealRead tailRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle N pkg ∧ PkgSig bundle routeRead pkg ∧
                PkgSig bundle sealRead pkg ∧ PkgSig bundle tailRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro tailRead ⟨hsame_refl tailRead, tailUnary⟩
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
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, routeCont, sealCont, tailCont, provenancePkg, namePkg, routePkg,
          sealPkg, tailPkg⟩
  }
  exact ⟨cert, routeUnary, sealUnary, tailUnary⟩

end BEDC.Derived.DyadicUp
