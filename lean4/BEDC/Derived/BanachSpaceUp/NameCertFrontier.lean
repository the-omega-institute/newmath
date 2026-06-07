import BEDC.Derived.BanachSpaceUp

namespace BEDC.Derived.BanachSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BanachSpaceNameCertFrontier [AskSetup] [PackageSetup]
    {V N M Q S R E Z H C P L analyticRead terminalRead frontierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory V →
      UnaryHistory N →
        UnaryHistory Q →
          UnaryHistory S →
            UnaryHistory R →
              UnaryHistory E →
                UnaryHistory Z →
                  Cont V N analyticRead →
                    Cont Q S terminalRead →
                      Cont terminalRead Z frontierRead →
                        PkgSig bundle P pkg →
                          PkgSig bundle L pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row V ∨ hsame row N ∨ hsame row Q ∨ hsame row S ∨
                                    hsame row R ∨ hsame row E ∨ hsame row Z ∨
                                      hsame row P ∨ hsame row L ∨ hsame row frontierRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont V N analyticRead ∧
                                    Cont Q S terminalRead ∧
                                      Cont terminalRead Z frontierRead ∧
                                        PkgSig bundle P pkg ∧ PkgSig bundle L pkg)
                                hsame ∧
                              UnaryHistory analyticRead ∧ UnaryHistory terminalRead ∧
                                UnaryHistory frontierRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro vUnary nUnary qUnary sUnary rUnary eUnary zUnary analyticRoute terminalRoute
    frontierRoute provenancePkg localPkg
  have analyticUnary : UnaryHistory analyticRead :=
    unary_cont_closed vUnary nUnary analyticRoute
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed qUnary sUnary terminalRoute
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed terminalUnary zUnary frontierRoute
  have sourceFrontier :
      (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row) frontierRead := by
    exact ⟨hsame_refl frontierRead, frontierUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V ∨ hsame row N ∨ hsame row Q ∨ hsame row S ∨
              hsame row R ∨ hsame row E ∨ hsame row Z ∨ hsame row P ∨ hsame row L ∨
                hsame row frontierRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont V N analyticRead ∧ Cont Q S terminalRead ∧
              Cont terminalRead Z frontierRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle L pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro frontierRead sourceFrontier
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
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, analyticRoute, terminalRoute, frontierRoute, provenancePkg,
          localPkg⟩
  }
  exact ⟨cert, analyticUnary, terminalUnary, frontierUnary⟩

end BEDC.Derived.BanachSpaceUp
