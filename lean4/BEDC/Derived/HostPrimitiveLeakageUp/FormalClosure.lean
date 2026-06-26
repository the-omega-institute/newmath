import BEDC.Derived.HostPrimitiveLeakageUp.RouteCertificates

namespace BEDC.Derived.HostPrimitiveLeakageUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HostPrimitiveLeakageNameCertObligations [AskSetup] [PackageSetup]
    {site request replacement diagnostic failedGate auditBoundary transport replay provenance name
      diagnosticRead replacementRead auditRead nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    hostPrimitiveLeakageFields
        (HostPrimitiveLeakageUp.mk site request replacement diagnostic failedGate auditBoundary
          transport replay provenance name) =
      [site, request, replacement, diagnostic, failedGate, auditBoundary, transport, replay,
        provenance, name] →
      UnaryHistory site →
        UnaryHistory diagnostic →
            UnaryHistory replacement →
              UnaryHistory failedGate →
                UnaryHistory auditBoundary →
                  UnaryHistory replay →
                    UnaryHistory name →
                      Cont site diagnostic diagnosticRead →
                        Cont replacement replay replacementRead →
                          Cont failedGate auditBoundary auditRead →
                            Cont diagnosticRead name nameRead →
                              PkgSig bundle provenance pkg →
                                PkgSig bundle name pkg →
                                  SemanticNameCert
                                  (fun row : BHist =>
                                    (hsame row diagnosticRead ∨ hsame row replacementRead ∨
                                          hsame row auditRead ∨ hsame row nameRead) ∧
                                      UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row site ∨ hsame row request ∨
                                      hsame row replacement ∨ hsame row diagnostic ∨
                                        hsame row failedGate ∨ hsame row auditBoundary ∨
                                          hsame row transport ∨ hsame row replay ∨
                                            hsame row provenance ∨ hsame row name ∨
                                              hsame row diagnosticRead ∨
                                                hsame row replacementRead ∨
                                                  hsame row auditRead ∨ hsame row nameRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont site diagnostic diagnosticRead ∧
                                      Cont replacement replay replacementRead ∧
                                        Cont failedGate auditBoundary auditRead ∧
                                          Cont diagnosticRead name nameRead ∧
                                            PkgSig bundle provenance pkg ∧
                                              PkgSig bundle name pkg)
                                  hsame ∧
                                    UnaryHistory diagnosticRead ∧
                                      UnaryHistory replacementRead ∧
                                        UnaryHistory auditRead ∧ UnaryHistory nameRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro fields_eq siteUnary diagnosticUnary replacementUnary failedGateUnary auditBoundaryUnary
    replayUnary nameUnary diagnosticRoute replacementRoute auditRoute nameRoute provenancePkg namePkg
  cases fields_eq
  have diagnosticReadUnary : UnaryHistory diagnosticRead :=
    unary_cont_closed siteUnary diagnosticUnary diagnosticRoute
  have replacementReadUnary : UnaryHistory replacementRead :=
    unary_cont_closed replacementUnary replayUnary replacementRoute
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed failedGateUnary auditBoundaryUnary auditRoute
  have nameReadUnary : UnaryHistory nameRead :=
    unary_cont_closed diagnosticReadUnary nameUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row diagnosticRead ∨ hsame row replacementRead ∨ hsame row auditRead ∨
                hsame row nameRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row site ∨ hsame row request ∨ hsame row replacement ∨
              hsame row diagnostic ∨ hsame row failedGate ∨ hsame row auditBoundary ∨
                hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                  hsame row name ∨ hsame row diagnosticRead ∨ hsame row replacementRead ∨
                    hsame row auditRead ∨ hsame row nameRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont site diagnostic diagnosticRead ∧
              Cont replacement replay replacementRead ∧ Cont failedGate auditBoundary auditRead ∧
                Cont diagnosticRead name nameRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle name pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro diagnosticRead
          ⟨Or.inl (hsame_refl diagnosticRead), diagnosticReadUnary⟩
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
        constructor
        · cases source.left with
          | inl diagnosticSame =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) diagnosticSame)
          | inr rest =>
              cases rest with
              | inl replacementSame =>
                  exact Or.inr
                    (Or.inl (hsame_trans (hsame_symm sameRows) replacementSame))
              | inr rest =>
                  cases rest with
                  | inl auditSame =>
                      exact Or.inr
                        (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) auditSame)))
                  | inr nameSame =>
                      exact Or.inr
                        (Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) nameSame)))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl diagnosticSame =>
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inr
          exact Or.inl diagnosticSame
      | inr rest =>
          cases rest with
          | inl replacementSame =>
              apply Or.inr
              apply Or.inr
              apply Or.inr
              apply Or.inr
              apply Or.inr
              apply Or.inr
              apply Or.inr
              apply Or.inr
              apply Or.inr
              apply Or.inr
              exact Or.inr (Or.inl replacementSame)
          | inr rest =>
              cases rest with
              | inl auditSame =>
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  exact Or.inr (Or.inr (Or.inl auditSame))
              | inr nameSame =>
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  apply Or.inr
                  exact Or.inr (Or.inr (Or.inr nameSame))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, diagnosticRoute, replacementRoute, auditRoute, nameRoute,
          provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, diagnosticReadUnary, replacementReadUnary, auditReadUnary, nameReadUnary⟩

theorem HostPrimitiveLeakageFormalTarget [AskSetup] [PackageSetup]
    {site request replacement diagnostic failedGate auditBoundary transport replay provenance name
      diagnosticRead replacementRead gateRead publicRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    hostPrimitiveLeakageFields
        (HostPrimitiveLeakageUp.mk site request replacement diagnostic failedGate auditBoundary
          transport replay provenance name) =
      [site, request, replacement, diagnostic, failedGate, auditBoundary, transport, replay,
        provenance, name] →
      UnaryHistory site →
        UnaryHistory diagnostic →
          UnaryHistory replacement →
            UnaryHistory failedGate →
              UnaryHistory auditBoundary →
                UnaryHistory replay →
                  UnaryHistory name →
                    Cont site diagnostic diagnosticRead →
                      Cont replacement replay replacementRead →
                        Cont failedGate auditBoundary gateRead →
                          Cont diagnosticRead replacementRead publicRead →
                            Cont publicRead name exportRead →
                              PkgSig bundle provenance pkg →
                                PkgSig bundle name pkg →
                                  PkgSig bundle exportRead pkg →
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row exportRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row site ∨ hsame row request ∨
                                            hsame row replacement ∨ hsame row diagnostic ∨
                                              hsame row failedGate ∨
                                                hsame row auditBoundary ∨
                                                  hsame row provenance ∨ hsame row name ∨
                                                    hsame row diagnosticRead ∨
                                                      hsame row replacementRead ∨
                                                        hsame row gateRead ∨
                                                          hsame row publicRead ∨
                                                            hsame row exportRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧
                                            Cont site diagnostic diagnosticRead ∧
                                              Cont replacement replay replacementRead ∧
                                                Cont failedGate auditBoundary gateRead ∧
                                                  Cont diagnosticRead replacementRead
                                                    publicRead ∧
                                                    Cont publicRead name exportRead ∧
                                                      PkgSig bundle provenance pkg ∧
                                                        PkgSig bundle name pkg ∧
                                                          PkgSig bundle exportRead pkg)
                                        hsame ∧
                                      UnaryHistory diagnosticRead ∧
                                        UnaryHistory replacementRead ∧
                                          UnaryHistory gateRead ∧
                                            UnaryHistory publicRead ∧
                                              UnaryHistory exportRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro fields_eq siteUnary diagnosticUnary replacementUnary failedGateUnary auditBoundaryUnary
    replayUnary nameUnary diagnosticRoute replacementRoute gateRoute publicRoute exportRoute
    provenancePkg namePkg exportPkg
  cases fields_eq
  have diagnosticReadUnary : UnaryHistory diagnosticRead :=
    unary_cont_closed siteUnary diagnosticUnary diagnosticRoute
  have replacementReadUnary : UnaryHistory replacementRead :=
    unary_cont_closed replacementUnary replayUnary replacementRoute
  have gateReadUnary : UnaryHistory gateRead :=
    unary_cont_closed failedGateUnary auditBoundaryUnary gateRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed diagnosticReadUnary replacementReadUnary publicRoute
  have exportReadUnary : UnaryHistory exportRead :=
    unary_cont_closed publicReadUnary nameUnary exportRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row site ∨ hsame row request ∨ hsame row replacement ∨
              hsame row diagnostic ∨ hsame row failedGate ∨ hsame row auditBoundary ∨
                hsame row provenance ∨ hsame row name ∨ hsame row diagnosticRead ∨
                  hsame row replacementRead ∨ hsame row gateRead ∨ hsame row publicRead ∨
                    hsame row exportRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont site diagnostic diagnosticRead ∧
              Cont replacement replay replacementRead ∧ Cont failedGate auditBoundary gateRead ∧
                Cont diagnosticRead replacementRead publicRead ∧ Cont publicRead name exportRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle exportRead pkg)
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
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, diagnosticRoute, replacementRoute, gateRoute, publicRoute,
          exportRoute, provenancePkg, namePkg, exportPkg⟩
  }
  exact
    ⟨cert, diagnosticReadUnary, replacementReadUnary, gateReadUnary, publicReadUnary,
      exportReadUnary⟩

end BEDC.Derived.HostPrimitiveLeakageUp
