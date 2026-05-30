import BEDC.Derived.MachineReadableAuditInterfaceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MachineReadableAuditInterfaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MachineReadableAuditInterfaceCarrier [AskSetup] [PackageSetup]
    (S C E R F H K P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory S ∧ UnaryHistory C ∧ UnaryHistory E ∧ UnaryHistory R ∧
    UnaryHistory F ∧ UnaryHistory H ∧ UnaryHistory K ∧ UnaryHistory P ∧
      UnaryHistory N ∧ Cont S C E ∧ Cont R F H ∧ Cont H K P ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem MachineReadableAuditInterface_obligation_basis [AskSetup] [PackageSetup]
    {S C E R F H K P N schemaRead reportRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MachineReadableAuditInterfaceCarrier S C E R F H K P N bundle pkg ->
      Cont S C schemaRead ->
        Cont E R reportRead ->
          Cont reportRead K replayRead ->
            PkgSig bundle replayRead pkg ->
              UnaryHistory S ∧ UnaryHistory C ∧ UnaryHistory E ∧ UnaryHistory R ∧
                UnaryHistory F ∧ UnaryHistory K ∧ UnaryHistory N ∧
                  UnaryHistory schemaRead ∧ UnaryHistory reportRead ∧
                    UnaryHistory replayRead ∧ Cont S C schemaRead ∧
                      Cont E R reportRead ∧ Cont reportRead K replayRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                          PkgSig bundle replayRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier schemaRoute reportRoute replayRoute replayPkg
  obtain ⟨SUnary, CUnary, EUnary, RUnary, FUnary, _HUnary, KUnary, _PUnary,
    NUnary, _schemaCarrierRoute, _reportCarrierRoute, _replayCarrierRoute,
    carrierPkg, namePkg⟩ := carrier
  have schemaUnary : UnaryHistory schemaRead :=
    unary_cont_closed SUnary CUnary schemaRoute
  have reportUnary : UnaryHistory reportRead :=
    unary_cont_closed EUnary RUnary reportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed reportUnary KUnary replayRoute
  exact
    ⟨SUnary, CUnary, EUnary, RUnary, FUnary, KUnary, NUnary, schemaUnary,
      reportUnary, replayUnary, schemaRoute, reportRoute, replayRoute, carrierPkg,
      namePkg, replayPkg⟩

theorem MachineReadableAuditInterface_non_evidence_refusal [AskSetup] [PackageSetup]
    {S C E R F H K P N refusalRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MachineReadableAuditInterfaceCarrier S C E R F H K P N bundle pkg ->
      Cont R F refusalRead ->
        Cont refusalRead K replayRead ->
          PkgSig bundle replayRead pkg ->
            UnaryHistory R ∧ UnaryHistory F ∧ UnaryHistory K ∧ UnaryHistory refusalRead ∧
              UnaryHistory replayRead ∧ Cont R F refusalRead ∧ Cont refusalRead K replayRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧ PkgSig bundle replayRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier refusalRoute replayRoute replayPkg
  obtain ⟨_SUnary, _CUnary, _EUnary, RUnary, FUnary, _HUnary, KUnary, _PUnary,
    _NUnary, _schemaCarrierRoute, _reportCarrierRoute, _replayCarrierRoute,
    carrierPkg, namePkg⟩ := carrier
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed RUnary FUnary refusalRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed refusalUnary KUnary replayRoute
  exact
    ⟨RUnary, FUnary, KUnary, refusalUnary, replayUnary, refusalRoute, replayRoute,
      carrierPkg, namePkg, replayPkg⟩

theorem MachineReadableAuditInterface_kernel_scope [AskSetup] [PackageSetup]
    {S C E R F H K P N schemaRead exportRead refusalRead reportRead scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MachineReadableAuditInterfaceCarrier S C E R F H K P N bundle pkg ->
      Cont S C schemaRead ->
        Cont E R exportRead ->
          Cont R F refusalRead ->
            Cont F K reportRead ->
              Cont reportRead N scopedRead ->
                PkgSig bundle scopedRead pkg ->
                  UnaryHistory S ∧ UnaryHistory C ∧ UnaryHistory E ∧ UnaryHistory R ∧
                    UnaryHistory F ∧ UnaryHistory K ∧ UnaryHistory N ∧
                      UnaryHistory schemaRead ∧ UnaryHistory exportRead ∧
                        UnaryHistory refusalRead ∧ UnaryHistory reportRead ∧
                          UnaryHistory scopedRead ∧ Cont S C schemaRead ∧
                            Cont E R exportRead ∧ Cont R F refusalRead ∧
                              Cont F K reportRead ∧ Cont reportRead N scopedRead ∧
                                PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                                  PkgSig bundle scopedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier schemaRoute exportRoute refusalRoute reportRoute scopedRoute scopedPkg
  obtain ⟨SUnary, CUnary, EUnary, RUnary, FUnary, _HUnary, KUnary, _PUnary,
    NUnary, _schemaCarrierRoute, _reportCarrierRoute, _replayCarrierRoute,
    carrierPkg, namePkg⟩ := carrier
  have schemaUnary : UnaryHistory schemaRead :=
    unary_cont_closed SUnary CUnary schemaRoute
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed EUnary RUnary exportRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed RUnary FUnary refusalRoute
  have reportUnary : UnaryHistory reportRead :=
    unary_cont_closed FUnary KUnary reportRoute
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed reportUnary NUnary scopedRoute
  exact
    ⟨SUnary, CUnary, EUnary, RUnary, FUnary, KUnary, NUnary, schemaUnary,
      exportUnary, refusalUnary, reportUnary, scopedUnary, schemaRoute, exportRoute,
      refusalRoute, reportRoute, scopedRoute, carrierPkg, namePkg, scopedPkg⟩

theorem MachineReadableAuditInterface_falsifiable_prediction [AskSetup] [PackageSetup]
    {S C E R F H K P N exportRead refusalRead reportRead verdictRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MachineReadableAuditInterfaceCarrier S C E R F H K P N bundle pkg ->
      Cont E R exportRead ->
        Cont R F refusalRead ->
          Cont F K reportRead ->
            Cont reportRead N verdictRead ->
              PkgSig bundle verdictRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row verdictRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row E ∨ hsame row R ∨ hsame row F ∨ hsame row K ∨
                        hsame row N ∨ hsame row exportRead ∨ hsame row refusalRead ∨
                          hsame row reportRead ∨ hsame row verdictRead)
                    (fun row : BHist =>
                      hsame row verdictRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle verdictRead pkg)
                    hsame ∧
                  UnaryHistory exportRead ∧ UnaryHistory refusalRead ∧
                    UnaryHistory reportRead ∧ UnaryHistory verdictRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig SemanticNameCert
  intro carrier exportRoute refusalRoute reportRoute verdictRoute verdictPkg
  obtain ⟨_SUnary, _CUnary, EUnary, RUnary, FUnary, _HUnary, KUnary, _PUnary,
    NUnary, _schemaCarrierRoute, _reportCarrierRoute, _replayCarrierRoute,
    carrierPkg, _namePkg⟩ := carrier
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed EUnary RUnary exportRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed RUnary FUnary refusalRoute
  have reportUnary : UnaryHistory reportRead :=
    unary_cont_closed FUnary KUnary reportRoute
  have verdictUnary : UnaryHistory verdictRead :=
    unary_cont_closed reportUnary NUnary verdictRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row verdictRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row E ∨ hsame row R ∨ hsame row F ∨ hsame row K ∨ hsame row N ∨
              hsame row exportRead ∨ hsame row refusalRead ∨ hsame row reportRead ∨
                hsame row verdictRead)
          (fun row : BHist =>
            hsame row verdictRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle verdictRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro verdictRead ⟨hsame_refl verdictRead, verdictUnary⟩
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
        intro _row other sameRows source
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
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, carrierPkg, verdictPkg⟩
  }
  exact ⟨cert, exportUnary, refusalUnary, reportUnary, verdictUnary⟩

theorem MachineReadableAuditInterface_sibling_independence [AskSetup] [PackageSetup]
    {S C E R F H K P N reportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MachineReadableAuditInterfaceCarrier S C E R F H K P N bundle pkg ->
      Cont E R reportRead ->
        PkgSig bundle reportRead pkg ->
          SemanticNameCert
                (fun row : BHist => hsame row reportRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row S ∨ hsame row C ∨ hsame row E ∨ hsame row R ∨
                    hsame row F ∨ hsame row reportRead)
                (fun row : BHist =>
                  hsame row reportRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle reportRead pkg)
                hsame ∧
              UnaryHistory S ∧ UnaryHistory C ∧ UnaryHistory E ∧ UnaryHistory R ∧
                UnaryHistory F ∧ UnaryHistory reportRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig SemanticNameCert
  intro carrier reportRoute reportPkg
  obtain ⟨SUnary, CUnary, EUnary, RUnary, FUnary, _HUnary, _KUnary, _PUnary,
    _NUnary, _schemaCarrierRoute, _reportCarrierRoute, _replayCarrierRoute,
    carrierPkg, _namePkg⟩ := carrier
  have reportUnary : UnaryHistory reportRead :=
    unary_cont_closed EUnary RUnary reportRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row reportRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row C ∨ hsame row E ∨ hsame row R ∨ hsame row F ∨
              hsame row reportRead)
          (fun row : BHist =>
            hsame row reportRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle reportRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro reportRead ⟨hsame_refl reportRead, reportUnary⟩
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
        intro _row other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, carrierPkg, reportPkg⟩
  }
  exact ⟨cert, SUnary, CUnary, EUnary, RUnary, FUnary, reportUnary⟩

end BEDC.Derived.MachineReadableAuditInterfaceUp
