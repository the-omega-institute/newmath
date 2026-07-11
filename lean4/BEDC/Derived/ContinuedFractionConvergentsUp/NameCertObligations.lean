import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.ContinuedFractionConvergentsUp.TasteGate

namespace BEDC.Derived.ContinuedFractionConvergentsUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuedFractionConvergentsNameCertObligations [AskSetup] [PackageSetup]
    {A N D Q W E R S H C P L rationalRead windowRead regularRead sealedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont A N rationalRead →
      Cont rationalRead D Q →
        Cont Q W windowRead →
          Cont windowRead E regularRead →
            Cont regularRead S sealedRead →
              UnaryHistory A →
                UnaryHistory N →
                  UnaryHistory D →
                    UnaryHistory W →
                      UnaryHistory E →
                        UnaryHistory S →
                          PkgSig bundle P pkg →
                            PkgSig bundle L pkg →
                              SemanticNameCert
                                  (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row A ∨ hsame row N ∨ hsame row D ∨
                                      hsame row Q ∨ hsame row W ∨ hsame row E ∨
                                        hsame row R ∨ hsame row S ∨ hsame row H ∨
                                          hsame row C ∨ hsame row P ∨ hsame row L ∨
                                            hsame row sealedRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont A N rationalRead ∧
                                      Cont rationalRead D Q ∧ Cont Q W windowRead ∧
                                        Cont windowRead E regularRead ∧
                                          Cont regularRead S sealedRead ∧
                                            PkgSig bundle L pkg)
                                  hsame ∧
                                UnaryHistory rationalRead ∧ UnaryHistory Q ∧
                                  UnaryHistory windowRead ∧ UnaryHistory regularRead ∧
                                    UnaryHistory sealedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro rationalRoute convergentRoute windowRoute regularRoute sealRoute aUnary nUnary
    dUnary wUnary eUnary sUnary _provenancePkg localPkg
  have rationalUnary : UnaryHistory rationalRead :=
    unary_cont_closed aUnary nUnary rationalRoute
  have qUnary : UnaryHistory Q :=
    unary_cont_closed rationalUnary dUnary convergentRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed qUnary wUnary windowRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed windowUnary eUnary regularRoute
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed regularUnary sUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row N ∨ hsame row D ∨ hsame row Q ∨ hsame row W ∨
              hsame row E ∨ hsame row R ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row L ∨ hsame row sealedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A N rationalRead ∧ Cont rationalRead D Q ∧
              Cont Q W windowRead ∧ Cont windowRead E regularRead ∧
                Cont regularRead S sealedRead ∧ PkgSig bundle L pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealedRead ⟨hsame_refl sealedRead, sealedUnary⟩
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
                                (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, rationalRoute, convergentRoute, windowRoute, regularRoute, sealRoute,
          localPkg⟩
  }
  exact ⟨cert, rationalUnary, qUnary, windowUnary, regularUnary, sealedUnary⟩

end BEDC.Derived.ContinuedFractionConvergentsUp
