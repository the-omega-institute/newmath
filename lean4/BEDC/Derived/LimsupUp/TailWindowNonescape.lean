import BEDC.Derived.LimsupUp

namespace BEDC.Derived.LimsupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LimsupTailWindowNonescape [AskSetup] [PackageSetup]
    {S U D T H C P N tailWindow upperRead lowerRead sealRead named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LimsupCarrier S U D T H C P N bundle pkg →
      Cont S U tailWindow →
        Cont tailWindow D upperRead →
          Cont upperRead H lowerRead →
            Cont lowerRead T sealRead →
              Cont sealRead C named →
                PkgSig bundle named pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row named ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row S ∨ hsame row U ∨ hsame row D ∨ hsame row H ∨
                          hsame row C ∨ hsame row tailWindow ∨ hsame row upperRead ∨
                            hsame row lowerRead ∨ hsame row sealRead ∨ hsame row named)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont S U tailWindow ∧
                          Cont tailWindow D upperRead ∧ Cont upperRead H lowerRead ∧
                            Cont lowerRead T sealRead ∧ Cont sealRead C named ∧
                              PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                                PkgSig bundle named pkg)
                      hsame ∧
                    UnaryHistory tailWindow ∧ UnaryHistory upperRead ∧
                      UnaryHistory lowerRead ∧ UnaryHistory sealRead ∧
                        UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier tailRoute upperRoute lowerRoute sealRoute namedRoute namedPkg
  obtain ⟨sUnary, uUnary, dUnary, _tUnary, hUnary, cUnary, _nUnary,
    _sourceUpperTransport, _transportLedgerReplay, provenancePkg, namePkg⟩ := carrier
  have tailUnary : UnaryHistory tailWindow :=
    unary_cont_closed sUnary uUnary tailRoute
  have upperUnary : UnaryHistory upperRead :=
    unary_cont_closed tailUnary dUnary upperRoute
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed upperUnary hUnary lowerRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed lowerUnary _tUnary sealRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed sealUnary cUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row U ∨ hsame row D ∨ hsame row H ∨ hsame row C ∨
              hsame row tailWindow ∨ hsame row upperRead ∨ hsame row lowerRead ∨
                hsame row sealRead ∨ hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S U tailWindow ∧ Cont tailWindow D upperRead ∧
              Cont upperRead H lowerRead ∧ Cont lowerRead T sealRead ∧
                Cont sealRead C named ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
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
        ⟨source.right, tailRoute, upperRoute, lowerRoute, sealRoute, namedRoute,
          provenancePkg, namePkg, namedPkg⟩
  }
  exact ⟨cert, tailUnary, upperUnary, lowerUnary, sealUnary, namedUnary⟩

end BEDC.Derived.LimsupUp
