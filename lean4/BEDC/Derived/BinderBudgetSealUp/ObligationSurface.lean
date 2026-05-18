import BEDC.Derived.BinderBudgetSealUp.CarrierAdmission

namespace BEDC.Derived.BinderBudgetSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BinderBudgetSealObligationSurface
    [AskSetup] [PackageSetup]
    {depth term payload shiftRoute substRoute transport contRoute provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BinderBudgetSealCarrier depth term payload shiftRoute substRoute transport contRoute
        provenance name bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            BinderBudgetSealCarrier depth term payload shiftRoute substRoute transport contRoute
              provenance name bundle pkg ∧ hsame row name)
          (fun row : BHist =>
            Cont depth term shiftRoute ∧ Cont depth payload substRoute ∧
              Cont shiftRoute substRoute contRoute ∧ hsame row name)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧ hsame row name)
          hsame ∧
        Cont depth term shiftRoute ∧ Cont depth payload substRoute ∧
          Cont shiftRoute substRoute contRoute := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier
  have carrierWitness := carrier
  obtain ⟨_depthUnary, _termUnary, _payloadUnary, _shiftRouteUnary, _substRouteUnary,
    _transportUnary, _contRouteUnary, _provenanceUnary, _nameUnary, depthTermShift,
    depthPayloadSubst, shiftSubstCont, provenancePkg, namePkg⟩ := carrier
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          BinderBudgetSealCarrier depth term payload shiftRoute substRoute transport contRoute
            provenance name bundle pkg ∧ hsame row name)
        (fun row : BHist =>
          Cont depth term shiftRoute ∧ Cont depth payload substRoute ∧
            Cont shiftRoute substRoute contRoute ∧ hsame row name)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧ hsame row name)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro name (And.intro carrierWitness (hsame_refl name))
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
        exact And.intro sourceRow.left
          (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact ⟨depthTermShift, depthPayloadSubst, shiftSubstCont, sourceRow.right⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨provenancePkg, namePkg, sourceRow.right⟩
  }
  exact ⟨cert, depthTermShift, depthPayloadSubst, shiftSubstCont⟩

end BEDC.Derived.BinderBudgetSealUp
