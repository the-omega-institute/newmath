import BEDC.Derived.LimsupUp

namespace BEDC.Derived.LimsupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LimsupScopedTailCutExhaustion [AskSetup] [PackageSetup]
    {S U D T H C P N upperRead lowerRead sealRead named audit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LimsupCarrier S U D T H C P N bundle pkg →
      Cont S U upperRead →
        Cont upperRead D lowerRead →
          Cont lowerRead T sealRead →
            Cont sealRead H named →
              Cont named C audit →
                PkgSig bundle audit pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row audit ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row S ∨ hsame row U ∨ hsame row D ∨ hsame row T ∨
                          hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                            hsame row upperRead ∨ hsame row lowerRead ∨
                              hsame row sealRead ∨ hsame row named ∨ hsame row audit)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont S U upperRead ∧
                          Cont upperRead D lowerRead ∧ Cont lowerRead T sealRead ∧
                            Cont sealRead H named ∧ Cont named C audit ∧
                              PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                                PkgSig bundle audit pkg)
                      hsame ∧
                    UnaryHistory upperRead ∧ UnaryHistory lowerRead ∧
                      UnaryHistory sealRead ∧ UnaryHistory named ∧ UnaryHistory audit := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier upperRoute lowerRoute sealRoute namedRoute auditRoute auditPkg
  obtain
    ⟨sUnary, uUnary, dUnary, tUnary, hUnary, cUnary, _nUnary,
      _sourceUpperTransport, _transportLedgerReplay, provenancePkg, namePkg⟩ := carrier
  have upperUnary : UnaryHistory upperRead :=
    unary_cont_closed sUnary uUnary upperRoute
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed upperUnary dUnary lowerRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed lowerUnary tUnary sealRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed sealUnary hUnary namedRoute
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed namedUnary cUnary auditRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row audit ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row U ∨ hsame row D ∨ hsame row T ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row upperRead ∨
                hsame row lowerRead ∨ hsame row sealRead ∨ hsame row named ∨
                  hsame row audit)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S U upperRead ∧ Cont upperRead D lowerRead ∧
              Cont lowerRead T sealRead ∧ Cont sealRead H named ∧ Cont named C audit ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧ PkgSig bundle audit pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro audit ⟨hsame_refl audit, auditUnary⟩
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
                              (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, upperRoute, lowerRoute, sealRoute, namedRoute, auditRoute,
          provenancePkg, namePkg, auditPkg⟩
  }
  exact ⟨cert, upperUnary, lowerUnary, sealUnary, namedUnary, auditUnary⟩

end BEDC.Derived.LimsupUp
