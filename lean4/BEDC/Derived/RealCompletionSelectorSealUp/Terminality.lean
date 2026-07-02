import BEDC.Derived.RealCompletionSelectorSealUp

namespace BEDC.Derived.RealCompletionSelectorSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCompletionSelectorSealTerminality [AskSetup] [PackageSetup]
    {b w r l e h c p n selectedWindow readbackRead limitRead endpointRead terminalRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCompletionSelectorSealCarrier b w r l e h c p n bundle pkg →
      Cont b w selectedWindow →
        Cont selectedWindow r readbackRead →
          Cont readbackRead l limitRead →
            Cont limitRead e endpointRead →
              Cont endpointRead c terminalRead →
                PkgSig bundle terminalRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row b ∨ hsame row w ∨ hsame row r ∨ hsame row l ∨
                          hsame row e ∨ hsame row terminalRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont b w selectedWindow ∧
                          Cont selectedWindow r readbackRead ∧
                            Cont readbackRead l limitRead ∧
                              Cont limitRead e endpointRead ∧
                                Cont endpointRead c terminalRead ∧
                                  PkgSig bundle terminalRead pkg)
                      hsame ∧
                    UnaryHistory selectedWindow ∧ UnaryHistory readbackRead ∧
                      UnaryHistory limitRead ∧ UnaryHistory endpointRead ∧
                        UnaryHistory terminalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier selectedRoute readbackRoute limitRoute endpointRoute terminalRoute
    terminalPkg
  have bUnary : UnaryHistory b := carrier.left
  have wUnary : UnaryHistory w := carrier.right.left
  have rUnary : UnaryHistory r := carrier.right.right.left
  have lUnary : UnaryHistory l := carrier.right.right.right.left
  have eUnary : UnaryHistory e := carrier.right.right.right.right.left
  have cUnary : UnaryHistory c := carrier.right.right.right.right.right.right.left
  have selectedUnary : UnaryHistory selectedWindow :=
    unary_cont_closed bUnary wUnary selectedRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed selectedUnary rUnary readbackRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed readbackUnary lUnary limitRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed limitUnary eUnary endpointRoute
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed endpointUnary cUnary terminalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row b ∨ hsame row w ∨ hsame row r ∨ hsame row l ∨ hsame row e ∨
              hsame row terminalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont b w selectedWindow ∧
              Cont selectedWindow r readbackRead ∧ Cont readbackRead l limitRead ∧
                Cont limitRead e endpointRead ∧ Cont endpointRead c terminalRead ∧
                  PkgSig bundle terminalRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro terminalRead
        ⟨hsame_refl terminalRead, terminalUnary⟩
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
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, selectedRoute, readbackRoute, limitRoute, endpointRoute,
          terminalRoute, terminalPkg⟩
  }
  exact
    ⟨cert, selectedUnary, readbackUnary, limitUnary, endpointUnary, terminalUnary⟩

end BEDC.Derived.RealCompletionSelectorSealUp
