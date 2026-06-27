import BEDC.Derived.RegularCauchyMinUp.SelectorIdempotence
import BEDC.Derived.RegularCauchyMinUp.SelectorLedger
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

theorem RegularCauchyMinCarrier_realalgorder_handoff [AskSetup] [PackageSetup]
    {A B W DA DB J S R E H C P N leftWindow rightWindow leftLedger rightLedger
      selectorRead handoffRead sealRead replayRead : BHist}
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
                        Cont A W leftWindow ->
                          Cont B W rightWindow ->
                            Cont leftWindow DA leftLedger ->
                              Cont rightWindow DB rightLedger ->
                                Cont J S selectorRead ->
                                  Cont selectorRead R handoffRead ->
                                    Cont handoffRead E sealRead ->
                                      Cont sealRead C replayRead ->
                                        PkgSig bundle P pkg ->
                                          PkgSig bundle N pkg ->
                                            SemanticNameCert
                                                (fun row : BHist =>
                                                  hsame row replayRead ∧ UnaryHistory row)
                                                (fun row : BHist =>
                                                  hsame row A ∨ hsame row B ∨
                                                    hsame row W ∨ hsame row DA ∨
                                                      hsame row DB ∨ hsame row J ∨
                                                        hsame row S ∨ hsame row R ∨
                                                          hsame row E ∨ hsame row H ∨
                                                            hsame row C ∨ hsame row P ∨
                                                              hsame row N ∨
                                                                hsame row replayRead)
                                                (fun row : BHist =>
                                                  UnaryHistory row ∧
                                                    Cont A W leftWindow ∧
                                                      Cont B W rightWindow ∧
                                                        Cont leftWindow DA leftLedger ∧
                                                          Cont rightWindow DB rightLedger ∧
                                                            Cont J S selectorRead ∧
                                                              Cont selectorRead R
                                                                handoffRead ∧
                                                                Cont handoffRead E sealRead ∧
                                                                  Cont sealRead C
                                                                    replayRead ∧
                                                                    PkgSig bundle P pkg ∧
                                                                      PkgSig bundle N pkg)
                                                hsame ∧
                                              UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro aUnary bUnary wUnary daUnary dbUnary jUnary sUnary rUnary eUnary cUnary
    leftWindowRoute rightWindowRoute leftLedgerRoute rightLedgerRoute selectorRoute
    handoffRoute sealRoute replayRoute provenancePkg namePkg
  have leftWindowUnary : UnaryHistory leftWindow :=
    unary_cont_closed aUnary wUnary leftWindowRoute
  have rightWindowUnary : UnaryHistory rightWindow :=
    unary_cont_closed bUnary wUnary rightWindowRoute
  have _leftLedgerUnary : UnaryHistory leftLedger :=
    unary_cont_closed leftWindowUnary daUnary leftLedgerRoute
  have _rightLedgerUnary : UnaryHistory rightLedger :=
    unary_cont_closed rightWindowUnary dbUnary rightLedgerRoute
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed jUnary sUnary selectorRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed selectorUnary rUnary handoffRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed handoffUnary eUnary sealRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed sealUnary cUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row B ∨ hsame row W ∨ hsame row DA ∨
              hsame row DB ∨ hsame row J ∨ hsame row S ∨ hsame row R ∨
                hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                  hsame row N ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A W leftWindow ∧ Cont B W rightWindow ∧
              Cont leftWindow DA leftLedger ∧ Cont rightWindow DB rightLedger ∧
                Cont J S selectorRead ∧ Cont selectorRead R handoffRead ∧
                  Cont handoffRead E sealRead ∧ Cont sealRead C replayRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
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
                              (Or.inr
                                (Or.inr source.left))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, leftWindowRoute, rightWindowRoute, leftLedgerRoute,
          rightLedgerRoute, selectorRoute, handoffRoute, sealRoute, replayRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, replayUnary⟩

end BEDC.Derived.RegularCauchyMinUp
