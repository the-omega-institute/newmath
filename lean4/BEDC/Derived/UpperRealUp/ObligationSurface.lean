import BEDC.Derived.UpperRealUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.UpperRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UpperRealCarrier_obligation_surface [AskSetup] [PackageSetup]
    {U0 L W R E H C P N upperRead windowRead handoffRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory U0 -> UnaryHistory L -> UnaryHistory W -> UnaryHistory R ->
      UnaryHistory E -> UnaryHistory N ->
        Cont U0 L upperRead -> Cont upperRead W windowRead ->
          Cont windowRead R handoffRead -> Cont handoffRead E sealRead ->
            Cont sealRead N namedRead -> PkgSig bundle P pkg ->
              PkgSig bundle namedRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row U0 ∨ hsame row L ∨ hsame row W ∨ hsame row R ∨
                        hsame row E ∨ hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont handoffRead E sealRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
                    hsame ∧
                  UnaryHistory upperRead ∧ UnaryHistory windowRead ∧
                    UnaryHistory handoffRead ∧ UnaryHistory sealRead ∧
                      UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro u0Unary _lUnary wUnary rUnary eUnary nUnary upperRoute windowRoute
    handoffRoute sealRoute namedRoute pkgP pkgNamed
  have upperUnary : UnaryHistory upperRead :=
    unary_cont_closed u0Unary _lUnary upperRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed upperUnary wUnary windowRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed windowUnary rUnary handoffRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed handoffUnary eUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U0 ∨ hsame row L ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
              hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont handoffRead E sealRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle namedRead pkg)
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
      exact ⟨source.right, sealRoute, pkgP, pkgNamed⟩
  }
  exact ⟨cert, upperUnary, windowUnary, handoffUnary, sealUnary, namedUnary⟩

theorem UpperRealCarrier_lower_upper_apartness_window [AskSetup] [PackageSetup]
    {U0 L W R H C apartRead windowRead regularRead transportRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory U0 -> UnaryHistory L -> UnaryHistory W -> UnaryHistory R ->
      UnaryHistory H -> UnaryHistory C ->
        Cont L U0 apartRead -> Cont apartRead W windowRead ->
          Cont windowRead R regularRead -> Cont regularRead H transportRead ->
            Cont transportRead C replayRead -> PkgSig bundle replayRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row U0 ∨ hsame row L ∨ hsame row W ∨ hsame row R ∨
                      hsame row H ∨ hsame row C ∨ hsame row replayRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont L U0 apartRead ∧
                      Cont apartRead W windowRead ∧ Cont windowRead R regularRead ∧
                        Cont regularRead H transportRead ∧
                          Cont transportRead C replayRead ∧
                            PkgSig bundle replayRead pkg)
                  hsame ∧
                UnaryHistory apartRead ∧ UnaryHistory windowRead ∧
                  UnaryHistory regularRead ∧ UnaryHistory transportRead ∧
                    UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro u0Unary lUnary wUnary rUnary hUnary cUnary apartRoute windowRoute
    regularRoute transportRoute replayRoute replayPkg
  have apartUnary : UnaryHistory apartRead :=
    unary_cont_closed lUnary u0Unary apartRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed apartUnary wUnary windowRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed windowUnary rUnary regularRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed regularUnary hUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary cUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U0 ∨ hsame row L ∨ hsame row W ∨ hsame row R ∨
              hsame row H ∨ hsame row C ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L U0 apartRead ∧
              Cont apartRead W windowRead ∧ Cont windowRead R regularRead ∧
                Cont regularRead H transportRead ∧ Cont transportRead C replayRead ∧
                  PkgSig bundle replayRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, apartRoute, windowRoute, regularRoute, transportRoute, replayRoute,
          replayPkg⟩
  }
  exact ⟨cert, apartUnary, windowUnary, regularUnary, transportUnary, replayUnary⟩

end BEDC.Derived.UpperRealUp
