import BEDC.Derived.RegularCauchyMinUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyMinUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyMinCarrier_obligation_classifier_scope [AskSetup] [PackageSetup]
    {A B W DA DB J S R E H C P N selectedRead readbackRead sealRead classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory A ->
      UnaryHistory B ->
        UnaryHistory W ->
          UnaryHistory DA ->
            UnaryHistory DB ->
              UnaryHistory J ->
                UnaryHistory S ->
                  UnaryHistory R ->
                    UnaryHistory E ->
                      UnaryHistory C ->
                        Cont J S selectedRead ->
                          Cont selectedRead R readbackRead ->
                            Cont readbackRead E sealRead ->
                              Cont sealRead C classifierRead ->
                                PkgSig bundle P pkg ->
                                  PkgSig bundle N pkg ->
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row classifierRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row A ∨ hsame row B ∨ hsame row W ∨
                                            hsame row DA ∨ hsame row DB ∨ hsame row J ∨
                                              hsame row S ∨ hsame row R ∨ hsame row E ∨
                                                hsame row H ∨ hsame row C ∨ hsame row P ∨
                                                  hsame row N ∨ hsame row classifierRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont J S selectedRead ∧
                                            Cont selectedRead R readbackRead ∧
                                              Cont readbackRead E sealRead ∧
                                                Cont sealRead C classifierRead ∧
                                                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                        hsame ∧
                                      UnaryHistory selectedRead ∧ UnaryHistory readbackRead ∧
                                        UnaryHistory sealRead ∧ UnaryHistory classifierRead := by
  -- BEDC touchpoint anchor: RegularCauchyMinUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro _aUnary _bUnary _wUnary _daUnary _dbUnary jUnary sUnary rUnary eUnary cUnary
    selectedRoute readbackRoute sealRoute classifierRoute pPkg nPkg
  have selectedUnary : UnaryHistory selectedRead :=
    unary_cont_closed jUnary sUnary selectedRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed selectedUnary rUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed sealUnary cUnary classifierRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row B ∨ hsame row W ∨ hsame row DA ∨ hsame row DB ∨
              hsame row J ∨ hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row classifierRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont J S selectedRead ∧ Cont selectedRead R readbackRead ∧
              Cont readbackRead E sealRead ∧ Cont sealRead C classifierRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
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
                          (Or.inr
                            (Or.inr
                              (Or.inr (Or.inr source.left))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, selectedRoute, readbackRoute, sealRoute, classifierRoute, pPkg, nPkg⟩
  }
  exact ⟨cert, selectedUnary, readbackUnary, sealUnary, classifierUnary⟩

end BEDC.Derived.RegularCauchyMinUp
