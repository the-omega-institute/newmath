import BEDC.Derived.HostPrimitiveLeakageUp.TasteGate

namespace BEDC.Derived.HostPrimitiveLeakageUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HostPrimitiveLeakageQuotSoundnessNonescape [AskSetup] [PackageSetup]
    {site request replacement diagnostic failedGate auditBoundary transport replay provenance name
      diagnosticRead quotientRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    hostPrimitiveLeakageFields
        (HostPrimitiveLeakageUp.mk site request replacement diagnostic failedGate auditBoundary
          transport replay provenance name) =
      [site, request, replacement, diagnostic, failedGate, auditBoundary, transport, replay,
        provenance, name] →
      UnaryHistory site →
        UnaryHistory diagnostic →
          UnaryHistory request →
            Cont site diagnostic diagnosticRead →
              Cont diagnosticRead request quotientRead →
                PkgSig bundle provenance pkg →
                  PkgSig bundle name pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row quotientRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row site ∨ hsame row request ∨ hsame row diagnostic ∨
                            hsame row failedGate ∨ hsame row auditBoundary ∨
                              hsame row provenance ∨ hsame row name ∨
                                hsame row diagnosticRead ∨ hsame row quotientRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont site diagnostic diagnosticRead ∧
                            Cont diagnosticRead request quotientRead ∧
                              PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg)
                        hsame ∧
                      UnaryHistory diagnosticRead ∧ UnaryHistory quotientRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro fields_eq siteUnary diagnosticUnary requestUnary diagnosticRoute quotientRoute
    provenancePkg namePkg
  cases fields_eq
  have diagnosticReadUnary : UnaryHistory diagnosticRead :=
    unary_cont_closed siteUnary diagnosticUnary diagnosticRoute
  have quotientReadUnary : UnaryHistory quotientRead :=
    unary_cont_closed diagnosticReadUnary requestUnary quotientRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row quotientRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row site ∨ hsame row request ∨ hsame row diagnostic ∨
              hsame row failedGate ∨ hsame row auditBoundary ∨ hsame row provenance ∨
                hsame row name ∨ hsame row diagnosticRead ∨ hsame row quotientRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont site diagnostic diagnosticRead ∧
              Cont diagnosticRead request quotientRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle name pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro quotientRead ⟨hsame_refl quotientRead, quotientReadUnary⟩
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
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, diagnosticRoute, quotientRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, diagnosticReadUnary, quotientReadUnary⟩

theorem HostPrimitiveLeakageAuditGateFactorization [AskSetup] [PackageSetup]
    {site request replacement diagnostic failedGate auditBoundary transport replay provenance name
      gateRead structuralRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    hostPrimitiveLeakageFields
        (HostPrimitiveLeakageUp.mk site request replacement diagnostic failedGate auditBoundary
          transport replay provenance name) =
      [site, request, replacement, diagnostic, failedGate, auditBoundary, transport, replay,
        provenance, name] →
      UnaryHistory failedGate →
        UnaryHistory auditBoundary →
          UnaryHistory transport →
            UnaryHistory replay →
              Cont failedGate auditBoundary gateRead →
                Cont gateRead transport structuralRead →
                  Cont structuralRead replay exportRead →
                    PkgSig bundle provenance pkg →
                      PkgSig bundle name pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row failedGate ∨ hsame row auditBoundary ∨
                                hsame row transport ∨ hsame row replay ∨
                                  hsame row provenance ∨ hsame row name ∨
                                    hsame row gateRead ∨ hsame row structuralRead ∨
                                      hsame row exportRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont failedGate auditBoundary gateRead ∧
                                Cont gateRead transport structuralRead ∧
                                  Cont structuralRead replay exportRead ∧
                                    PkgSig bundle provenance pkg ∧
                                      PkgSig bundle name pkg)
                            hsame ∧
                          UnaryHistory gateRead ∧ UnaryHistory structuralRead ∧
                            UnaryHistory exportRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro fields_eq failedGateUnary auditBoundaryUnary transportUnary replayUnary gateRoute
    structuralRoute exportRoute provenancePkg namePkg
  cases fields_eq
  have gateReadUnary : UnaryHistory gateRead :=
    unary_cont_closed failedGateUnary auditBoundaryUnary gateRoute
  have structuralReadUnary : UnaryHistory structuralRead :=
    unary_cont_closed gateReadUnary transportUnary structuralRoute
  have exportReadUnary : UnaryHistory exportRead :=
    unary_cont_closed structuralReadUnary replayUnary exportRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row failedGate ∨ hsame row auditBoundary ∨ hsame row transport ∨
              hsame row replay ∨ hsame row provenance ∨ hsame row name ∨
                hsame row gateRead ∨ hsame row structuralRead ∨ hsame row exportRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont failedGate auditBoundary gateRead ∧
              Cont gateRead transport structuralRead ∧ Cont structuralRead replay exportRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exportRead ⟨hsame_refl exportRead, exportReadUnary⟩
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
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, gateRoute, structuralRoute, exportRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, gateReadUnary, structuralReadUnary, exportReadUnary⟩

end BEDC.Derived.HostPrimitiveLeakageUp
