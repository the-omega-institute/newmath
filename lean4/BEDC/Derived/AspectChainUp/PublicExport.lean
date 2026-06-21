import BEDC.Derived.AspectChainUp.ConsumerBoundary

namespace BEDC.Derived.AspectChainUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AspectChainPublicExport [AskSetup] [PackageSetup] {x : AspectChainUp}
    {records inscription gap locality otherMinds transport routes provenance nameCert recordsRead
      localityRead observerRead publicRead : BHist}
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
                  Cont records inscription recordsRead →
                    Cont gap locality localityRead →
                      Cont otherMinds routes observerRead →
                        Cont recordsRead observerRead publicRead →
                          PkgSig bundle provenance pkg →
                            PkgSig bundle nameCert pkg →
                              SemanticNameCert
                                  (fun row : BHist =>
                                    hsame row publicRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row records ∨ hsame row inscription ∨
                                      hsame row gap ∨ hsame row locality ∨
                                        hsame row otherMinds ∨ hsame row transport ∨
                                          hsame row routes ∨ hsame row provenance ∨
                                            hsame row nameCert ∨ hsame row publicRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont records inscription recordsRead ∧
                                      Cont gap locality localityRead ∧
                                        Cont otherMinds routes observerRead ∧
                                          Cont recordsRead observerRead publicRead ∧
                                            PkgSig bundle provenance pkg ∧
                                              PkgSig bundle nameCert pkg)
                                  hsame ∧
                                UnaryHistory recordsRead ∧ UnaryHistory localityRead ∧
                                  UnaryHistory observerRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro hx recordsUnary inscriptionUnary gapUnary localityUnary otherMindsUnary routesUnary
    recordsRoute localityRoute observerRoute publicRoute provenancePkg nameCertPkg
  cases hx
  have recordsReadUnary : UnaryHistory recordsRead :=
    unary_cont_closed recordsUnary inscriptionUnary recordsRoute
  have localityReadUnary : UnaryHistory localityRead :=
    unary_cont_closed gapUnary localityUnary localityRoute
  have observerReadUnary : UnaryHistory observerRead :=
    unary_cont_closed otherMindsUnary routesUnary observerRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed recordsReadUnary observerReadUnary publicRoute
  have sourcePublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead := by
    exact ⟨hsame_refl publicRead, publicReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row records ∨ hsame row inscription ∨ hsame row gap ∨
              hsame row locality ∨ hsame row otherMinds ∨ hsame row transport ∨
                hsame row routes ∨ hsame row provenance ∨ hsame row nameCert ∨
                  hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont records inscription recordsRead ∧
              Cont gap locality localityRead ∧ Cont otherMinds routes observerRead ∧
                Cont recordsRead observerRead publicRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle nameCert pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourcePublic
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
        ⟨source.right, recordsRoute, localityRoute, observerRoute, publicRoute,
          provenancePkg, nameCertPkg⟩
  }
  exact ⟨cert, recordsReadUnary, localityReadUnary, observerReadUnary, publicReadUnary⟩

end BEDC.Derived.AspectChainUp
