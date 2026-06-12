import BEDC.Derived.DiagonalLimitBudgetUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DiagonalLimitBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitBudgetCarrierAdmission [AskSetup] [PackageSetup]
    {x : DiagonalLimitBudgetUp}
    {D M W Q E H C P N requestBudget selectedWindow dyadicRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    x = DiagonalLimitBudgetUp.mk D M W Q E H C P N ->
      UnaryHistory D ->
        UnaryHistory M ->
          UnaryHistory W ->
            UnaryHistory Q ->
              UnaryHistory E ->
                Cont D M requestBudget ->
                  Cont requestBudget W selectedWindow ->
                    Cont selectedWindow Q dyadicRead ->
                      Cont dyadicRead E sealRead ->
                        PkgSig bundle P pkg ->
                          PkgSig bundle N pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row D ∨ hsame row M ∨ hsame row W ∨
                                    hsame row Q ∨ hsame row E ∨ hsame row N ∨
                                      Cont dyadicRead E sealRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont D M requestBudget ∧
                                    Cont requestBudget W selectedWindow ∧
                                      Cont selectedWindow Q dyadicRead ∧
                                        Cont dyadicRead E sealRead ∧
                                          PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory requestBudget ∧ UnaryHistory selectedWindow ∧
                                UnaryHistory dyadicRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier dUnary mUnary wUnary qUnary eUnary requestRoute windowRoute dyadicRoute
    sealRoute provenancePkg namePkg
  have _acceptedCarrier :
      x = DiagonalLimitBudgetUp.mk D M W Q E H C P N := carrier
  have requestUnary : UnaryHistory requestBudget :=
    unary_cont_closed dUnary mUnary requestRoute
  have selectedUnary : UnaryHistory selectedWindow :=
    unary_cont_closed requestUnary wUnary windowRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed selectedUnary qUnary dyadicRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row M ∨ hsame row W ∨ hsame row Q ∨ hsame row E ∨
              hsame row N ∨ Cont dyadicRead E sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D M requestBudget ∧
              Cont requestBudget W selectedWindow ∧ Cont selectedWindow Q dyadicRead ∧
                Cont dyadicRead E sealRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      intro _row _source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr sealRoute)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, requestRoute, windowRoute, dyadicRoute, sealRoute, provenancePkg,
          namePkg⟩
  }
  exact ⟨cert, requestUnary, selectedUnary, dyadicUnary, sealUnary⟩

end BEDC.Derived.DiagonalLimitBudgetUp
