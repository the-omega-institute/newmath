import BEDC.Derived.RegularCauchyTelescopingBudgetUp.RealSealHandoff

namespace BEDC.Derived.RegularCauchyTelescopingBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyTelescopingBudgetCarrier_nonescape [AskSetup] [PackageSetup]
    {E W D R S T C P N precisionRead ledgerRead telescopingRead handoffRead sealRead
      replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory E →
      UnaryHistory W →
        UnaryHistory D →
          UnaryHistory T →
            UnaryHistory R →
              UnaryHistory S →
                UnaryHistory C →
                  Cont E W precisionRead →
                    Cont precisionRead D ledgerRead →
                      Cont ledgerRead T telescopingRead →
                        Cont telescopingRead R handoffRead →
                          Cont handoffRead S sealRead →
                            Cont sealRead C replayRead →
                              PkgSig bundle P pkg →
                                PkgSig bundle N pkg →
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row replayRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row E ∨ hsame row W ∨ hsame row D ∨
                                          hsame row T ∨ hsame row R ∨ hsame row S ∨
                                            hsame row C ∨ hsame row P ∨ hsame row N ∨
                                              hsame row replayRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont E W precisionRead ∧
                                          Cont precisionRead D ledgerRead ∧
                                            Cont ledgerRead T telescopingRead ∧
                                              Cont telescopingRead R handoffRead ∧
                                                Cont handoffRead S sealRead ∧
                                                  Cont sealRead C replayRead ∧
                                                    PkgSig bundle P pkg ∧
                                                      PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory precisionRead ∧
                                      UnaryHistory ledgerRead ∧
                                        UnaryHistory telescopingRead ∧
                                          UnaryHistory handoffRead ∧
                                            UnaryHistory sealRead ∧
                                              UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro eUnary wUnary dUnary tUnary rUnary sUnary cUnary precisionRoute ledgerRoute
    telescopingRoute handoffRoute sealRoute replayRoute provenancePkg namePkg
  have precisionUnary : UnaryHistory precisionRead :=
    unary_cont_closed eUnary wUnary precisionRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed precisionUnary dUnary ledgerRoute
  have telescopingUnary : UnaryHistory telescopingRead :=
    unary_cont_closed ledgerUnary tUnary telescopingRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed telescopingUnary rUnary handoffRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed handoffUnary sUnary sealRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed sealUnary cUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row E ∨ hsame row W ∨ hsame row D ∨ hsame row T ∨ hsame row R ∨
              hsame row S ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont E W precisionRead ∧ Cont precisionRead D ledgerRead ∧
              Cont ledgerRead T telescopingRead ∧ Cont telescopingRead R handoffRead ∧
                Cont handoffRead S sealRead ∧ Cont sealRead C replayRead ∧
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
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, precisionRoute, ledgerRoute, telescopingRoute, handoffRoute,
          sealRoute, replayRoute, provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, precisionUnary, ledgerUnary, telescopingUnary, handoffUnary, sealUnary,
      replayUnary⟩

end BEDC.Derived.RegularCauchyTelescopingBudgetUp
