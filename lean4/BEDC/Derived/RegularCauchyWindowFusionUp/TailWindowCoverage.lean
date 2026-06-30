import BEDC.Derived.RegularCauchyWindowFusionUp.RealSealNonescape

namespace BEDC.Derived.RegularCauchyWindowFusionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyWindowFusionTailWindowCoverage [AskSetup] [PackageSetup]
    {R W S D E H _C P _N tailRead dyadicRead sealRead named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R →
      UnaryHistory W →
        UnaryHistory S →
          UnaryHistory D →
            UnaryHistory E →
              UnaryHistory H →
                Cont W S tailRead →
                  Cont tailRead D dyadicRead →
                    Cont dyadicRead E sealRead →
                      Cont H sealRead named →
                        PkgSig bundle P pkg →
                          PkgSig bundle named pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row named ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row W ∨ hsame row S ∨ hsame row D ∨
                                    hsame row E ∨ hsame row H ∨ hsame row tailRead ∨
                                      hsame row dyadicRead ∨ hsame row sealRead ∨
                                        hsame row named)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont W S tailRead ∧
                                    Cont tailRead D dyadicRead ∧
                                      Cont dyadicRead E sealRead ∧
                                        Cont H sealRead named ∧ PkgSig bundle named pkg)
                                hsame ∧
                              UnaryHistory tailRead ∧ UnaryHistory dyadicRead ∧
                                UnaryHistory sealRead ∧ UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro _rUnary wUnary sUnary dUnary eUnary hUnary tailRoute dyadicRoute sealRoute
    namedRoute _packageRead namedPkg
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed wUnary sUnary tailRoute
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed tailReadUnary dUnary dyadicRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicReadUnary eUnary sealRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed hUnary sealReadUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row S ∨ hsame row D ∨ hsame row E ∨ hsame row H ∨
              hsame row tailRead ∨ hsame row dyadicRead ∨ hsame row sealRead ∨
                hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W S tailRead ∧ Cont tailRead D dyadicRead ∧
              Cont dyadicRead E sealRead ∧ Cont H sealRead named ∧
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
                      (Or.inr sourceRow.left)))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, tailRoute, dyadicRoute, sealRoute, namedRoute, namedPkg⟩
  }
  exact ⟨cert, tailReadUnary, dyadicReadUnary, sealReadUnary, namedUnary⟩

theorem RegularCauchyWindowFusionTailStability [AskSetup] [PackageSetup]
    {R W S D E H C P N W' S' H' C' P' N' tailRead dyadicRead sealRead named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory W →
      UnaryHistory S →
        UnaryHistory D →
          UnaryHistory E →
            UnaryHistory H →
              UnaryHistory W' →
                UnaryHistory S' →
                  UnaryHistory H' →
                    Cont W' S' tailRead →
                      Cont tailRead D dyadicRead →
                        Cont dyadicRead E sealRead →
                          Cont H' sealRead named →
                            PkgSig bundle named pkg →
                              SemanticNameCert
                            (fun row : BHist => hsame row named ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row R ∨ hsame row W ∨ hsame row S ∨
                                hsame row D ∨ hsame row E ∨ hsame row H ∨
                                  hsame row C ∨ hsame row P ∨ hsame row N ∨
                                    hsame row W' ∨ hsame row S' ∨ hsame row H' ∨
                                      hsame row C' ∨ hsame row P' ∨ hsame row N' ∨
                                        hsame row named)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont W' S' tailRead ∧
                                Cont tailRead D dyadicRead ∧
                                  Cont dyadicRead E sealRead ∧
                                    Cont H' sealRead named ∧ PkgSig bundle named pkg)
                            hsame ∧
                                UnaryHistory tailRead ∧ UnaryHistory dyadicRead ∧
                                  UnaryHistory sealRead ∧ UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro _wUnary _sUnary dUnary eUnary _hUnary wTailUnary sTailUnary hTailUnary tailRoute
    dyadicRoute sealRoute namedRoute namedPkg
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed wTailUnary sTailUnary tailRoute
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed tailReadUnary dUnary dyadicRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicReadUnary eUnary sealRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed hTailUnary sealReadUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row W ∨ hsame row S ∨ hsame row D ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row W' ∨
                hsame row S' ∨ hsame row H' ∨ hsame row C' ∨ hsame row P' ∨
                  hsame row N' ∨ hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W' S' tailRead ∧ Cont tailRead D dyadicRead ∧
              Cont dyadicRead E sealRead ∧ Cont H' sealRead named ∧
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
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr sourceRow.left))))))))))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, tailRoute, dyadicRoute, sealRoute, namedRoute, namedPkg⟩
  }
  exact ⟨cert, tailReadUnary, dyadicReadUnary, sealReadUnary, namedUnary⟩

end BEDC.Derived.RegularCauchyWindowFusionUp
