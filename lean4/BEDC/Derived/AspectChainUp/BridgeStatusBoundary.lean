import BEDC.Derived.AspectChainUp.PublicExport

namespace BEDC.Derived.AspectChainUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AspectChain_bridge_status_boundary [AskSetup] [PackageSetup] {x : AspectChainUp}
    {records inscription gap locality otherMinds transport routes provenance nameCert publicRead
      bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    x =
        AspectChainUp.mk records inscription gap locality otherMinds transport routes provenance
          nameCert →
      UnaryHistory records →
        UnaryHistory inscription →
          UnaryHistory gap →
            UnaryHistory locality →
              UnaryHistory otherMinds →
                UnaryHistory routes →
                  UnaryHistory nameCert →
                    Cont records inscription publicRead →
                      Cont publicRead nameCert bridgeRead →
                        PkgSig bundle provenance pkg →
                          PkgSig bundle nameCert pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row records ∨ hsame row inscription ∨ hsame row gap ∨
                                    hsame row locality ∨ hsame row otherMinds ∨
                                      hsame row transport ∨ hsame row routes ∨
                                        hsame row provenance ∨ hsame row nameCert ∨
                                          hsame row publicRead ∨ hsame row bridgeRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont records inscription publicRead ∧
                                    Cont publicRead nameCert bridgeRead ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle nameCert pkg)
                                hsame ∧
                              UnaryHistory publicRead ∧ UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro hx recordsUnary inscriptionUnary _gapUnary _localityUnary _otherMindsUnary _routesUnary
    nameCertUnary publicRoute bridgeRoute provenancePkg nameCertPkg
  cases hx
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed recordsUnary inscriptionUnary publicRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed publicUnary nameCertUnary bridgeRoute
  have sourceBridge :
      (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row) bridgeRead := by
    exact ⟨hsame_refl bridgeRead, bridgeUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row records ∨ hsame row inscription ∨ hsame row gap ∨ hsame row locality ∨
              hsame row otherMinds ∨ hsame row transport ∨ hsame row routes ∨
                hsame row provenance ∨ hsame row nameCert ∨ hsame row publicRead ∨
                  hsame row bridgeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont records inscription publicRead ∧
              Cont publicRead nameCert bridgeRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle nameCert pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bridgeRead sourceBridge
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
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, publicRoute, bridgeRoute, provenancePkg, nameCertPkg⟩
  }
  exact ⟨cert, publicUnary, bridgeUnary⟩

end BEDC.Derived.AspectChainUp
