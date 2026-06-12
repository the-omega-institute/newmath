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

theorem TailCofinalityBudget_namecert_obligations [AskSetup] [PackageSetup]
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
                                hsame row consumer ∧ Cont R W D ∧
                                  Cont D Q windowRead ∧ Cont windowRead E sealRead ∧
                                    Cont sealRead N consumer)
                              (fun row : BHist => hsame row consumer ∧ PkgSig bundle N pkg)
                              hsame ∧
                            UnaryHistory D ∧ UnaryHistory windowRead ∧
                              UnaryHistory sealRead ∧ UnaryHistory consumer := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro _fields routeD routeWindow routeSeal routeConsumer unaryR unaryW unaryQ unaryE
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
          hsame row consumer ∧ Cont R W D ∧ Cont D Q windowRead ∧
            Cont windowRead E sealRead ∧ Cont sealRead N consumer)
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
      exact ⟨source.left, routeD, routeWindow, routeSeal, routeConsumer⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, namePkg⟩
  }
  exact ⟨cert, unaryD, unaryWindow, unarySeal, unaryConsumer⟩

theorem TailCofinalityBudgetClassifierObligation [AskSetup] [PackageSetup]
    {x y : TailCofinalityBudgetUp}
    {R W D Q E H C P N R' W' D' Q' E' H' C' P' N' windowRead sealRead
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    tailCofinalityBudgetFields x = [R, W, D, Q, E, H, C, P, N] →
      tailCofinalityBudgetFields y = [R', W', D', Q', E', H', C', P', N'] →
        hsame R R' →
          hsame W W' →
            hsame D D' →
              hsame Q Q' →
                hsame E E' →
                  UnaryHistory R →
                    UnaryHistory W →
                      UnaryHistory D →
                        UnaryHistory Q →
                          UnaryHistory E →
                            UnaryHistory N →
                              Cont R W D →
                                Cont D Q windowRead →
                                  Cont windowRead E sealRead →
                                    Cont sealRead N consumer →
                                      PkgSig bundle N pkg →
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row consumer ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row consumer ∧ hsame R R' ∧
                                                hsame W W' ∧ hsame D D' ∧
                                                  hsame Q Q' ∧ hsame E E' ∧
                                                    Cont R W D ∧
                                                      Cont D Q windowRead ∧
                                                        Cont windowRead E sealRead ∧
                                                          Cont sealRead N consumer)
                                            (fun row : BHist =>
                                              hsame row consumer ∧ PkgSig bundle N pkg)
                                            hsame := by
  -- BEDC touchpoint anchor: TailCofinalityBudgetUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro _fieldsX _fieldsY sameR sameW sameD sameQ sameE _unaryR _unaryW unaryD
    unaryQ unaryE unaryN routeD routeWindow routeSeal routeConsumer namePkg
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed unaryD unaryQ routeWindow
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary unaryE routeSeal
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed sealUnary unaryN routeConsumer
  exact {
    core := {
      carrier_inhabited := Exists.intro consumer ⟨hsame_refl consumer, consumerUnary⟩
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
        ⟨source.left, sameR, sameW, sameD, sameQ, sameE, routeD, routeWindow,
          routeSeal, routeConsumer⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, namePkg⟩
  }

end BEDC.Derived.TailCofinalityBudgetUp
