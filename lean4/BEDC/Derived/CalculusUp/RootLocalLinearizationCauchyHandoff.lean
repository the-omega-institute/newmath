import BEDC.Derived.CalculusUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusRootLocalLinearizationCauchyHandoff [AskSetup] [PackageSetup]
    {C D R Q Y _H _T P N derivativeRead dyadicRead realRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory C →
      UnaryHistory D →
        UnaryHistory Q →
          UnaryHistory Y →
            UnaryHistory R →
              UnaryHistory N →
                Cont C D derivativeRead →
                  Cont derivativeRead Q dyadicRead →
                    Cont Q Y realRead →
                      Cont realRead R namedRead →
                        PkgSig bundle P pkg →
                          PkgSig bundle N pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row C ∨ hsame row D ∨ hsame row Q ∨ hsame row Y ∨
                                    hsame row R ∨ hsame row namedRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont C D derivativeRead ∧
                                    Cont derivativeRead Q dyadicRead ∧
                                      Cont Q Y realRead ∧ Cont realRead R namedRead ∧
                                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory derivativeRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro cUnary dUnary qUnary yUnary rUnary _nUnary derivativeRoute dyadicRoute realRoute
    namedRoute provenancePkg namePkg
  have derivativeUnary : UnaryHistory derivativeRead :=
    unary_cont_closed cUnary dUnary derivativeRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed derivativeUnary qUnary dyadicRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed qUnary yUnary realRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed realUnary rUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row D ∨ hsame row Q ∨ hsame row Y ∨ hsame row R ∨
              hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C D derivativeRead ∧ Cont derivativeRead Q dyadicRead ∧
              Cont Q Y realRead ∧ Cont realRead R namedRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact
        ⟨source.right, derivativeRoute, dyadicRoute, realRoute, namedRoute, provenancePkg,
          namePkg⟩
  }
  exact ⟨cert, derivativeUnary, namedUnary⟩

end BEDC.Derived.CalculusUp
