import BEDC.Derived.RegularCauchyApartnessBudgetUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyApartnessBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyApartnessBudgetCarrier_route_composition [AskSetup] [PackageSetup]
    {X A M W D R E H C P N lowerRead realRead reciprocalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory A →
      UnaryHistory M →
        UnaryHistory W →
          UnaryHistory D →
            UnaryHistory R →
              UnaryHistory E →
                Cont A M W →
                  Cont W D lowerRead →
                    Cont lowerRead R realRead →
                      Cont realRead E reciprocalRead →
                        PkgSig bundle P pkg →
                          PkgSig bundle N pkg →
                            SemanticNameCert
                              (fun row : BHist => hsame row reciprocalRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row A ∨ hsame row W ∨ hsame row D ∨
                                  hsame row R ∨ hsame row realRead ∨
                                    hsame row reciprocalRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont A M W ∧ Cont W D lowerRead ∧
                                  Cont lowerRead R realRead ∧ Cont realRead E reciprocalRead ∧
                                    PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                              hsame ∧
                              UnaryHistory lowerRead ∧ UnaryHistory realRead ∧
                                UnaryHistory reciprocalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro aUnary mUnary wUnary dUnary rUnary eUnary budgetRoute lowerRoute realRoute
    reciprocalRoute packageP packageN
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed wUnary dUnary lowerRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed lowerUnary rUnary realRoute
  have reciprocalUnary : UnaryHistory reciprocalRead :=
    unary_cont_closed realUnary eUnary reciprocalRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row reciprocalRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row A ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
            hsame row realRead ∨ hsame row reciprocalRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont A M W ∧ Cont W D lowerRead ∧
            Cont lowerRead R realRead ∧ Cont realRead E reciprocalRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro reciprocalRead ⟨hsame_refl reciprocalRead, reciprocalUnary⟩
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
        ⟨source.right, budgetRoute, lowerRoute, realRoute, reciprocalRoute, packageP,
          packageN⟩
  }
  exact ⟨cert, lowerUnary, realUnary, reciprocalUnary⟩

end BEDC.Derived.RegularCauchyApartnessBudgetUp
