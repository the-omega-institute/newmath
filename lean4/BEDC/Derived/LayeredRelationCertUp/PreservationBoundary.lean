import BEDC.Derived.LayeredRelationCertUp.NameCertSurface

namespace BEDC.Derived.LayeredRelationCertUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LayeredRelationCertCarrier_preservation_boundary [AskSetup] [PackageSetup]
    {chainA chainB layerMap classifier preserved refused exactness failureBoundary strength
      transport route provenance nameRow publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory chainA →
      UnaryHistory layerMap →
        UnaryHistory preserved →
          UnaryHistory exactness →
          Cont chainA layerMap preserved →
            Cont preserved exactness publicRead →
              PkgSig bundle provenance pkg →
                PkgSig bundle nameRow pkg →
                  PkgSig bundle publicRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row chainA ∨ hsame row chainB ∨ hsame row layerMap ∨
                            hsame row classifier ∨ hsame row preserved ∨
                              hsame row refused ∨ hsame row exactness ∨
                                hsame row failureBoundary ∨ hsame row strength ∨
                                  hsame row transport ∨ hsame row route ∨
                                    hsame row provenance ∨ hsame row nameRow ∨
                                      hsame row publicRead)
                        (fun row : BHist =>
                          hsame row publicRead ∧ PkgSig bundle publicRead pkg)
                        hsame ∧
                      Cont chainA layerMap preserved ∧
                        Cont preserved exactness publicRead ∧
                          PkgSig bundle provenance pkg ∧
                            PkgSig bundle nameRow pkg ∧
                              PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro chainUnary layerUnary preservedUnary exactnessUnary preserveRoute publicRoute provenancePkg
    namePkg publicPkg
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed preservedUnary exactnessUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row chainA ∨ hsame row chainB ∨ hsame row layerMap ∨
              hsame row classifier ∨ hsame row preserved ∨ hsame row refused ∨
                hsame row exactness ∨ hsame row failureBoundary ∨ hsame row strength ∨
                  hsame row transport ∨ hsame row route ∨ hsame row provenance ∨
                    hsame row nameRow ∨ hsame row publicRead)
          (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead
        (And.intro (hsame_refl publicRead) publicUnary)
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
          And.intro (hsame_trans (hsame_symm sameRows) source.left)
            (unary_transport source.right sameRows)
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
      apply Or.inr
      exact source.left
    ledger_sound := by
      intro _row source
      exact And.intro source.left publicPkg
  }
  exact ⟨cert, preserveRoute, publicRoute, provenancePkg, namePkg, publicPkg⟩

end BEDC.Derived.LayeredRelationCertUp
