import BEDC.Derived.CauchyOscillationUp

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationRealCompletionAuditHandoff [AskSetup] [PackageSetup]
    {W M Q T S H C P N windowRead toleranceRead ledgerRead sealRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier W M Q T S H C P N bundle pkg →
      Cont W M windowRead →
        Cont windowRead Q toleranceRead →
          Cont toleranceRead T ledgerRead →
            Cont ledgerRead S sealRead →
              Cont sealRead N auditRead →
                PkgSig bundle auditRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row W ∨ hsame row M ∨ hsame row Q ∨ hsame row T ∨
                          hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                            hsame row N ∨ hsame row windowRead ∨
                              hsame row toleranceRead ∨ hsame row ledgerRead ∨
                                hsame row sealRead ∨ hsame row auditRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont W M windowRead ∧
                          Cont windowRead Q toleranceRead ∧
                            Cont toleranceRead T ledgerRead ∧
                              Cont ledgerRead S sealRead ∧ Cont sealRead N auditRead ∧
                                PkgSig bundle auditRead pkg)
                      hsame ∧
                    UnaryHistory windowRead ∧ UnaryHistory toleranceRead ∧
                      UnaryHistory ledgerRead ∧ UnaryHistory sealRead ∧
                        UnaryHistory auditRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier windowRoute toleranceRoute ledgerRoute sealRoute auditRoute auditPkg
  obtain ⟨wUnary, mUnary, qUnary, tUnary, sUnary, _hUnary, _cUnary, _pUnary, nUnary,
    _wmqRoute, _mqtRoute, _tshRoute, _hnpRoute, _pkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary mUnary windowRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowUnary qUnary toleranceRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed toleranceUnary tUnary ledgerRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed ledgerUnary sUnary sealRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed sealUnary nUnary auditRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row M ∨ hsame row Q ∨ hsame row T ∨ hsame row S ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row windowRead ∨ hsame row toleranceRead ∨ hsame row ledgerRead ∨
                  hsame row sealRead ∨ hsame row auditRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W M windowRead ∧ Cont windowRead Q toleranceRead ∧
              Cont toleranceRead T ledgerRead ∧ Cont ledgerRead S sealRead ∧
                Cont sealRead N auditRead ∧ PkgSig bundle auditRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro auditRead ⟨hsame_refl auditRead, auditUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, toleranceRoute, ledgerRoute, sealRoute, auditRoute,
          auditPkg⟩
  }
  exact ⟨cert, windowUnary, toleranceUnary, ledgerUnary, sealUnary, auditUnary⟩

end BEDC.Derived.CauchyOscillationUp
