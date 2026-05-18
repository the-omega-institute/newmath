import BEDC.Derived.BinderBudgetSealUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.BinderBudgetSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

def BinderBudgetSealCarrier [AskSetup] [PackageSetup]
    (depth term payload shiftRoute substRoute transport contRoute provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  UnaryHistory depth ∧ UnaryHistory term ∧ UnaryHistory payload ∧
    UnaryHistory shiftRoute ∧ UnaryHistory substRoute ∧ UnaryHistory transport ∧
      UnaryHistory contRoute ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont depth term shiftRoute ∧ Cont depth payload substRoute ∧
          Cont shiftRoute substRoute contRoute ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle name pkg

theorem BinderBudgetSealCarrierAdmission [AskSetup] [PackageSetup]
    {depth term payload shiftRoute substRoute transport contRoute provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BinderBudgetSealCarrier depth term payload shiftRoute substRoute transport contRoute
        provenance name bundle pkg ->
      UnaryHistory depth ∧ UnaryHistory term ∧ UnaryHistory payload ∧
        UnaryHistory shiftRoute ∧ UnaryHistory substRoute ∧ UnaryHistory transport ∧
          UnaryHistory contRoute ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
            Cont depth term shiftRoute ∧ Cont depth payload substRoute ∧
              Cont shiftRoute substRoute contRoute ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle name pkg ∧
                SemanticNameCert
                  (fun row : BHist =>
                    BinderBudgetSealCarrier depth term payload shiftRoute substRoute transport
                      contRoute provenance name bundle pkg ∧ hsame row name)
                  (fun row : BHist =>
                    Cont depth term shiftRoute ∧ Cont depth payload substRoute ∧
                      Cont shiftRoute substRoute contRoute ∧ hsame row name)
                  (fun row : BHist => PkgSig bundle name pkg ∧ hsame row name)
                  hsame := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier
  have carrierWitness := carrier
  obtain ⟨depthUnary, termUnary, payloadUnary, shiftRouteUnary, substRouteUnary,
    transportUnary, contRouteUnary, provenanceUnary, nameUnary, depthTermShift,
    depthPayloadSubst, shiftSubstCont, provenancePkg, namePkg⟩ := carrier
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          BinderBudgetSealCarrier depth term payload shiftRoute substRoute transport contRoute
            provenance name bundle pkg ∧ hsame row name)
        (fun row : BHist =>
          Cont depth term shiftRoute ∧ Cont depth payload substRoute ∧
            Cont shiftRoute substRoute contRoute ∧ hsame row name)
        (fun row : BHist => PkgSig bundle name pkg ∧ hsame row name)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro name (And.intro carrierWitness (hsame_refl name))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        exact And.intro sourceRow.left
          (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact ⟨depthTermShift, depthPayloadSubst, shiftSubstCont, sourceRow.right⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨namePkg, sourceRow.right⟩
  }
  exact
      ⟨depthUnary, termUnary, payloadUnary, shiftRouteUnary, substRouteUnary, transportUnary,
      contRouteUnary, provenanceUnary, nameUnary, depthTermShift, depthPayloadSubst,
        shiftSubstCont, provenancePkg, namePkg, cert⟩

end BEDC.Derived.BinderBudgetSealUp
