import BEDC.Derived.LayeredRelationCertUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LayeredRelationCertUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LayeredRelationCertCarrier_namecert_surface [AskSetup] [PackageSetup]
    {chainA chainB layerMap classifier preserved refused exactness failureBoundary strength
      transport route provenance nameRow publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory chainA ->
      UnaryHistory layerMap ->
        UnaryHistory refused ->
          UnaryHistory failureBoundary ->
            Cont chainA layerMap preserved ->
              Cont refused failureBoundary publicRead ->
                PkgSig bundle provenance pkg ->
                  PkgSig bundle nameRow pkg ->
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
                          UnaryHistory row ∧ Cont chainA layerMap preserved ∧
                            Cont refused failureBoundary publicRead ∧
                              PkgSig bundle provenance pkg ∧ PkgSig bundle nameRow pkg)
                        hsame ∧ UnaryHistory preserved ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro chainUnary layerUnary refusedUnary failureUnary preserveRoute publicRoute
    provenancePkg namePkg
  have preservedUnary : UnaryHistory preserved :=
    unary_cont_closed chainUnary layerUnary preserveRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed refusedUnary failureUnary publicRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row chainA ∨ hsame row chainB ∨ hsame row layerMap ∨
            hsame row classifier ∨ hsame row preserved ∨ hsame row refused ∨
              hsame row exactness ∨ hsame row failureBoundary ∨ hsame row strength ∨
                hsame row transport ∨ hsame row route ∨ hsame row provenance ∨
                  hsame row nameRow ∨ hsame row publicRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont chainA layerMap preserved ∧
            Cont refused failureBoundary publicRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle nameRow pkg)
        hsame := by
    refine
      { core := ?core
        pattern_sound := ?pattern_sound
        ledger_sound := ?ledger_sound }
    · refine
        { carrier_inhabited := ?carrier_inhabited
          equiv_refl := ?equiv_refl
          equiv_symm := ?equiv_symm
          equiv_trans := ?equiv_trans
          carrier_respects_equiv := ?carrier_respects_equiv }
      · exact Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other same
        exact hsame_symm same
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row other same source
        exact ⟨hsame_trans (hsame_symm same) source.left,
          unary_transport source.right same⟩
    · intro row source
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
    · intro row source
      exact ⟨source.right, preserveRoute, publicRoute, provenancePkg, namePkg⟩
  exact ⟨cert, preservedUnary, publicUnary⟩

end BEDC.Derived.LayeredRelationCertUp
