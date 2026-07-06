import BEDC.Derived.CauchyOscillationUp

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationMatureStatusRouteFormalTarget [AskSetup] [PackageSetup]
    {W M Q T S H C P N auditRead sealRead ledgerRead refusalRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier W M Q T S H C P N bundle pkg ->
      Cont W M auditRead -> Cont auditRead Q sealRead -> Cont Q T ledgerRead ->
        Cont sealRead H refusalRead -> Cont refusalRead C completionRead ->
          PkgSig bundle completionRead pkg ->
            SemanticNameCert (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row W ∨ hsame row M ∨ hsame row Q ∨
                hsame row T ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨
                  hsame row P ∨ hsame row N ∨ hsame row completionRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont W M auditRead ∧ Cont auditRead Q sealRead ∧
                  Cont Q T ledgerRead ∧ Cont sealRead H refusalRead ∧
                    Cont refusalRead C completionRead ∧ PkgSig bundle completionRead pkg)
              hsame ∧ UnaryHistory auditRead ∧ UnaryHistory sealRead ∧
                UnaryHistory ledgerRead ∧ UnaryHistory refusalRead ∧
                  UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier auditRoute sealRoute ledgerRoute refusalRoute completionRoute completionPkg
  obtain ⟨wUnary, mUnary, qUnary, tUnary, _sUnary, hUnary, cUnary, _pUnary,
    _nUnary, _carrierAudit, _carrierLedger, _carrierSeal, _carrierName, _carrierPkg⟩ :=
    carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed wUnary mUnary auditRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed auditUnary qUnary sealRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed qUnary tUnary ledgerRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed sealUnary hUnary refusalRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed refusalUnary cUnary completionRoute
  have cert :
      SemanticNameCert (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
        (fun row : BHist => hsame row W ∨ hsame row M ∨ hsame row Q ∨
          hsame row T ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
            hsame row N ∨ hsame row completionRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont W M auditRead ∧ Cont auditRead Q sealRead ∧
            Cont Q T ledgerRead ∧ Cont sealRead H refusalRead ∧
              Cont refusalRead C completionRead ∧ PkgSig bundle completionRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro completionRead
        ⟨hsame_refl completionRead, completionUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, auditRoute, sealRoute, ledgerRoute, refusalRoute, completionRoute,
          completionPkg⟩
  }
  exact ⟨cert, auditUnary, sealUnary, ledgerUnary, refusalUnary, completionUnary⟩

theorem CauchyOscillationMatureStatusRoute [AskSetup] [PackageSetup]
    {W M Q T S H C P N auditRead sealRead ledgerRead refusalRead completionRead
      bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier W M Q T S H C P N bundle pkg ->
      Cont W M auditRead -> Cont auditRead Q sealRead -> Cont Q T ledgerRead ->
        Cont sealRead H refusalRead -> Cont refusalRead C completionRead ->
          Cont completionRead N bridgeRead -> PkgSig bundle bridgeRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row W ∨ hsame row M ∨ hsame row Q ∨ hsame row T ∨
                    hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                      hsame row N ∨ hsame row bridgeRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont W M auditRead ∧ Cont auditRead Q sealRead ∧
                    Cont Q T ledgerRead ∧ Cont sealRead H refusalRead ∧
                      Cont refusalRead C completionRead ∧ Cont completionRead N bridgeRead ∧
                        PkgSig bundle bridgeRead pkg)
                hsame ∧ UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier auditRoute sealRoute ledgerRoute refusalRoute completionRoute bridgeRoute
    bridgePkg
  obtain ⟨wUnary, mUnary, qUnary, tUnary, _sUnary, hUnary, cUnary, _pUnary,
    nUnary, _carrierAudit, _carrierLedger, _carrierSeal, _carrierName, _carrierPkg⟩ :=
    carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed wUnary mUnary auditRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed auditUnary qUnary sealRoute
  have _ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed qUnary tUnary ledgerRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed sealUnary hUnary refusalRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed refusalUnary cUnary completionRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed completionUnary nUnary bridgeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row M ∨ hsame row Q ∨ hsame row T ∨
              hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row bridgeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W M auditRead ∧ Cont auditRead Q sealRead ∧
              Cont Q T ledgerRead ∧ Cont sealRead H refusalRead ∧
                Cont refusalRead C completionRead ∧ Cont completionRead N bridgeRead ∧
                  PkgSig bundle bridgeRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro bridgeRead ⟨hsame_refl bridgeRead, bridgeUnary⟩
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
      exact Or.inr
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
        ⟨source.right, auditRoute, sealRoute, ledgerRoute, refusalRoute, completionRoute,
          bridgeRoute, bridgePkg⟩
  }
  exact ⟨cert, bridgeUnary⟩

end BEDC.Derived.CauchyOscillationUp
