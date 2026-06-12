import BEDC.Derived.TailCofinalityBudgetUp.NameCertObligations
import BEDC.Derived.TailCofinalityBudgetUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TailCofinalityBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TailCofinalityBudgetCarrierObligation [AskSetup] [PackageSetup]
    {x : TailCofinalityBudgetUp}
    {R W D Q E H C P N windowRead sealRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    tailCofinalityBudgetFields x = [R, W, D, Q, E, H, C, P, N] ->
      Cont R W D ->
        Cont D Q windowRead ->
          Cont windowRead E sealRead ->
            Cont sealRead N consumer ->
              UnaryHistory R ->
                UnaryHistory W ->
                  UnaryHistory Q ->
                    UnaryHistory E ->
                      UnaryHistory N ->
                        PkgSig bundle N pkg ->
                          SemanticNameCert
                              (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row R ∨ hsame row W ∨ hsame row D ∨ hsame row Q ∨
                                  hsame row E ∨ hsame row consumer)
                              (fun row : BHist =>
                                hsame row consumer ∧ PkgSig bundle N pkg)
                              hsame ∧
                            UnaryHistory D ∧ UnaryHistory windowRead ∧
                              UnaryHistory sealRead ∧ UnaryHistory consumer := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro fields routeD routeWindow routeSeal routeConsumer unaryR unaryW unaryQ unaryE
    unaryN namePkg
  have unaryD : UnaryHistory D :=
    unary_cont_closed unaryR unaryW routeD
  have unaryWindow : UnaryHistory windowRead :=
    unary_cont_closed unaryD unaryQ routeWindow
  have unarySeal : UnaryHistory sealRead :=
    unary_cont_closed unaryWindow unaryE routeSeal
  have unaryConsumer : UnaryHistory consumer :=
    unary_cont_closed unarySeal unaryN routeConsumer
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row R ∨ hsame row W ∨ hsame row D ∨ hsame row Q ∨ hsame row E ∨
            hsame row consumer)
        (fun row : BHist => hsame row consumer ∧ PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro consumer ⟨hsame_refl consumer, unaryConsumer⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
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
      exact ⟨source.left, namePkg⟩
  }
  have _fieldsUsed :
      tailCofinalityBudgetFields x = [R, W, D, Q, E, H, C, P, N] :=
    fields
  exact ⟨cert, unaryD, unaryWindow, unarySeal, unaryConsumer⟩

theorem TailCofinalityBudgetObligationCarrier [AskSetup] [PackageSetup]
    {x : TailCofinalityBudgetUp}
    {R W D Q E H C P N windowRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    tailCofinalityBudgetFields x = [R, W, D, Q, E, H, C, P, N] ->
      Cont R W D ->
        Cont D Q windowRead ->
          Cont windowRead E sealRead ->
            Cont sealRead N namedRead ->
              UnaryHistory R ->
                UnaryHistory W ->
                  UnaryHistory Q ->
                    UnaryHistory E ->
                      UnaryHistory N ->
                        PkgSig bundle N pkg ->
                          PkgSig bundle namedRead pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row R ∨ hsame row W ∨ hsame row D ∨
                                    hsame row Q ∨ hsame row E ∨ hsame row namedRead)
                                (fun row : BHist =>
                                  hsame row namedRead ∧ PkgSig bundle namedRead pkg)
                                hsame ∧
                              UnaryHistory D ∧ UnaryHistory windowRead ∧
                                UnaryHistory sealRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: TailCofinalityBudgetUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro _fields routeD routeWindow routeSeal routeNamed unaryR unaryW unaryQ unaryE
    unaryN _namePkg namedPkg
  have unaryD : UnaryHistory D :=
    unary_cont_closed unaryR unaryW routeD
  have unaryWindow : UnaryHistory windowRead :=
    unary_cont_closed unaryD unaryQ routeWindow
  have unarySeal : UnaryHistory sealRead :=
    unary_cont_closed unaryWindow unaryE routeSeal
  have unaryNamed : UnaryHistory namedRead :=
    unary_cont_closed unarySeal unaryN routeNamed
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row W ∨ hsame row D ∨ hsame row Q ∨ hsame row E ∨
              hsame row namedRead)
          (fun row : BHist => hsame row namedRead ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, unaryNamed⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
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
      exact ⟨source.left, namedPkg⟩
  }
  exact ⟨cert, unaryD, unaryWindow, unarySeal, unaryNamed⟩

end BEDC.Derived.TailCofinalityBudgetUp
