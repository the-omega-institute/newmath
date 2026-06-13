import BEDC.Derived.RegularCauchyAffineCombinationUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyAffineCombinationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyAffineCombinationObligationSurface [AskSetup] [PackageSetup]
    {Q X Y WX WY DQ DbarQ SX SY Sigma E R Z H C P N coeffRead leftWindow rightWindow
      leftScale rightScale sumRead ledgerRead readbackRead sealRead localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory Q →
      UnaryHistory X →
        UnaryHistory Y →
          UnaryHistory WX →
            UnaryHistory WY →
              UnaryHistory DQ →
                UnaryHistory DbarQ →
                  UnaryHistory SX →
                    UnaryHistory SY →
                      UnaryHistory Sigma →
                        UnaryHistory E →
                          UnaryHistory R →
                            UnaryHistory Z →
                              UnaryHistory N →
                                Cont Q DQ coeffRead →
                                  Cont X WX leftWindow →
                                    Cont Y WY rightWindow →
                                      Cont leftWindow SX leftScale →
                                        Cont rightWindow SY rightScale →
                                          Cont leftScale rightScale sumRead →
                                            Cont sumRead E ledgerRead →
                                              Cont ledgerRead R readbackRead →
                                                Cont readbackRead Z sealRead →
                                                  Cont sealRead N localRead →
                                                    PkgSig bundle localRead pkg →
                                                      SemanticNameCert
                                                          (fun row : BHist =>
                                                            hsame row localRead ∧
                                                              UnaryHistory row)
                                                          (fun row : BHist =>
                                                            hsame row Q ∨ hsame row X ∨
                                                              hsame row Y ∨ hsame row WX ∨
                                                                hsame row WY ∨ hsame row DQ ∨
                                                                  hsame row DbarQ ∨
                                                                    hsame row SX ∨
                                                                      hsame row SY ∨
                                                                        hsame row Sigma ∨
                                                                          hsame row E ∨
                                                                            hsame row R ∨
                                                                              hsame row Z ∨
                                                                                hsame row H ∨
                                                                                  hsame row C ∨
                                                                                    hsame row P ∨
                                                                                      hsame row N ∨
                                                                                        hsame row localRead)
                                                          (fun row : BHist =>
                                                            UnaryHistory row ∧
                                                              Cont Q DQ coeffRead ∧
                                                                Cont X WX leftWindow ∧
                                                                  Cont Y WY rightWindow ∧
                                                                    Cont leftWindow SX leftScale ∧
                                                                      Cont rightWindow SY rightScale ∧
                                                                        Cont leftScale rightScale sumRead ∧
                                                                          Cont sumRead E ledgerRead ∧
                                                                            Cont ledgerRead R readbackRead ∧
                                                                              Cont readbackRead Z sealRead ∧
                                                                                Cont sealRead N localRead ∧
                                                                                  PkgSig bundle localRead pkg)
                                                          hsame ∧
                                                        UnaryHistory localRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame
  intro qUnary xUnary yUnary wxUnary wyUnary dqUnary _dbarqUnary sxUnary syUnary
    _sigmaUnary eUnary rUnary zUnary nUnary coeffRoute leftWindowRoute rightWindowRoute
    leftScaleRoute rightScaleRoute sumRoute ledgerRoute readbackRoute sealRoute localRoute
    localPkg
  have coeffUnary : UnaryHistory coeffRead :=
    unary_cont_closed qUnary dqUnary coeffRoute
  have leftWindowUnary : UnaryHistory leftWindow :=
    unary_cont_closed xUnary wxUnary leftWindowRoute
  have rightWindowUnary : UnaryHistory rightWindow :=
    unary_cont_closed yUnary wyUnary rightWindowRoute
  have leftScaleUnary : UnaryHistory leftScale :=
    unary_cont_closed leftWindowUnary sxUnary leftScaleRoute
  have rightScaleUnary : UnaryHistory rightScale :=
    unary_cont_closed rightWindowUnary syUnary rightScaleRoute
  have sumUnary : UnaryHistory sumRead :=
    unary_cont_closed leftScaleUnary rightScaleUnary sumRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed sumUnary eUnary ledgerRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed ledgerUnary rUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary zUnary sealRoute
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed sealUnary nUnary localRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row X ∨ hsame row Y ∨ hsame row WX ∨
              hsame row WY ∨ hsame row DQ ∨ hsame row DbarQ ∨ hsame row SX ∨
                hsame row SY ∨ hsame row Sigma ∨ hsame row E ∨ hsame row R ∨
                  hsame row Z ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                    hsame row N ∨ hsame row localRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q DQ coeffRead ∧ Cont X WX leftWindow ∧
              Cont Y WY rightWindow ∧ Cont leftWindow SX leftScale ∧
                Cont rightWindow SY rightScale ∧ Cont leftScale rightScale sumRead ∧
                  Cont sumRead E ledgerRead ∧ Cont ledgerRead R readbackRead ∧
                    Cont readbackRead Z sealRead ∧ Cont sealRead N localRead ∧
                      PkgSig bundle localRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localRead ⟨hsame_refl localRead, localUnary⟩
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left,
          unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr source.left))))))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, coeffRoute, leftWindowRoute, rightWindowRoute, leftScaleRoute,
          rightScaleRoute, sumRoute, ledgerRoute, readbackRoute, sealRoute, localRoute,
          localPkg⟩
  }
  exact ⟨cert, localUnary⟩

end BEDC.Derived.RegularCauchyAffineCombinationUp
