import BEDC.Derived.WronskianUp.CarrierObligation

namespace BEDC.Derived.WronskianUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem WronskianCarrier_sturm_separation_handoff [AskSetup] [PackageSetup]
    {F D J Omega S R E H C P N sturmRead rootRead sealRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WronskianObligationRowSpec F D J Omega S R E H C P N Omega →
      UnaryHistory Omega →
        UnaryHistory S →
          UnaryHistory R →
            UnaryHistory E →
              UnaryHistory H →
                Cont Omega S sturmRead →
                  Cont sturmRead R rootRead →
                    Cont rootRead E sealRead →
                      Cont sealRead H handoffRead →
                        PkgSig bundle handoffRead pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row Omega ∨ hsame row S ∨ hsame row R ∨
                                  hsame row E ∨ hsame row H ∨ hsame row sturmRead ∨
                                    hsame row rootRead ∨ hsame row sealRead ∨
                                      hsame row handoffRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont Omega S sturmRead ∧
                                  Cont sturmRead R rootRead ∧ Cont rootRead E sealRead ∧
                                    Cont sealRead H handoffRead ∧
                                      PkgSig bundle handoffRead pkg)
                              hsame ∧
                            UnaryHistory sturmRead ∧ UnaryHistory rootRead ∧
                              UnaryHistory sealRead ∧ UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro _omegaSpec omegaUnary sUnary rUnary eUnary hUnary sturmRoute rootRoute sealRoute
    handoffRoute handoffPkg
  have sturmUnary : UnaryHistory sturmRead :=
    unary_cont_closed omegaUnary sUnary sturmRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed sturmUnary rUnary rootRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed rootUnary eUnary sealRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed sealUnary hUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Omega ∨ hsame row S ∨ hsame row R ∨ hsame row E ∨
              hsame row H ∨ hsame row sturmRead ∨ hsame row rootRead ∨
                hsame row sealRead ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Omega S sturmRead ∧ Cont sturmRead R rootRead ∧
              Cont rootRead E sealRead ∧ Cont sealRead H handoffRead ∧
                PkgSig bundle handoffRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffUnary⟩
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
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sturmRoute, rootRoute, sealRoute, handoffRoute, handoffPkg⟩
  }
  exact ⟨cert, sturmUnary, rootUnary, sealUnary, handoffUnary⟩

end BEDC.Derived.WronskianUp
