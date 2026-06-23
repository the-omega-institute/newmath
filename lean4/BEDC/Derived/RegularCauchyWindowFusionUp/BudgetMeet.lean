import BEDC.Derived.RegularCauchyWindowFusionUp.NameCertObligations

namespace BEDC.Derived.RegularCauchyWindowFusionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyWindowFusionCarrier_budget_meet [AskSetup] [PackageSetup]
    {R W S D E _H _C P _N seedWindow regularDyadic sealMeet named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R →
      UnaryHistory W →
        UnaryHistory S →
          UnaryHistory D →
            UnaryHistory E →
              Cont R W seedWindow →
                Cont S D regularDyadic →
                  Cont seedWindow regularDyadic sealMeet →
                    Cont sealMeet E named →
                      PkgSig bundle P pkg →
                        PkgSig bundle named pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row named ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row R ∨ hsame row W ∨ hsame row S ∨
                                  hsame row D ∨ hsame row E ∨ hsame row sealMeet ∨
                                    hsame row named)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont R W seedWindow ∧
                                  Cont S D regularDyadic ∧
                                    Cont seedWindow regularDyadic sealMeet ∧
                                      Cont sealMeet E named ∧ PkgSig bundle named pkg)
                              hsame ∧
                            UnaryHistory seedWindow ∧ UnaryHistory regularDyadic ∧
                              UnaryHistory sealMeet ∧ UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro rUnary wUnary sUnary dUnary eUnary seedRoute dyadicRoute meetRoute namedRoute
    _packageRead namedPkg
  have seedUnary : UnaryHistory seedWindow :=
    unary_cont_closed rUnary wUnary seedRoute
  have regularDyadicUnary : UnaryHistory regularDyadic :=
    unary_cont_closed sUnary dUnary dyadicRoute
  have sealMeetUnary : UnaryHistory sealMeet :=
    unary_cont_closed seedUnary regularDyadicUnary meetRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed sealMeetUnary eUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row W ∨ hsame row S ∨ hsame row D ∨ hsame row E ∨
              hsame row sealMeet ∨ hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R W seedWindow ∧ Cont S D regularDyadic ∧
              Cont seedWindow regularDyadic sealMeet ∧ Cont sealMeet E named ∧
                PkgSig bundle named pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro named ⟨hsame_refl named, namedUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, seedRoute, dyadicRoute, meetRoute, namedRoute, namedPkg⟩
  }
  exact ⟨cert, seedUnary, regularDyadicUnary, sealMeetUnary, namedUnary⟩

theorem RegularCauchyWindowFusionTailBudgetMeet [AskSetup] [PackageSetup]
    {R W S D E H C P N tailRead budgetRead sealRead named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory W →
      UnaryHistory S →
        UnaryHistory D →
          UnaryHistory E →
            UnaryHistory H →
              Cont W S tailRead →
                Cont S D budgetRead →
                  Cont tailRead budgetRead sealRead →
                    Cont H sealRead named →
                      PkgSig bundle named pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row named ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row R ∨ hsame row W ∨ hsame row S ∨
                                hsame row D ∨ hsame row E ∨ hsame row H ∨
                                  hsame row C ∨ hsame row P ∨ hsame row N ∨
                                    hsame row tailRead ∨ hsame row budgetRead ∨
                                      hsame row sealRead ∨ hsame row named)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont W S tailRead ∧
                                Cont S D budgetRead ∧
                                  Cont tailRead budgetRead sealRead ∧
                                    Cont H sealRead named ∧ PkgSig bundle named pkg)
                            hsame ∧
                          UnaryHistory tailRead ∧ UnaryHistory budgetRead ∧
                            UnaryHistory sealRead ∧ UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro wUnary sUnary dUnary _eUnary hUnary tailRoute budgetRoute sealRoute namedRoute namedPkg
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed wUnary sUnary tailRoute
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed sUnary dUnary budgetRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailReadUnary budgetReadUnary sealRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed hUnary sealReadUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row W ∨ hsame row S ∨ hsame row D ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row tailRead ∨ hsame row budgetRead ∨ hsame row sealRead ∨
                  hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W S tailRead ∧ Cont S D budgetRead ∧
              Cont tailRead budgetRead sealRead ∧ Cont H sealRead named ∧
                PkgSig bundle named pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro named ⟨hsame_refl named, namedUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
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
                              (Or.inr sourceRow.left)))))))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, tailRoute, budgetRoute, sealRoute, namedRoute, namedPkg⟩
  }
  exact ⟨cert, tailReadUnary, budgetReadUnary, sealReadUnary, namedUnary⟩

end BEDC.Derived.RegularCauchyWindowFusionUp
