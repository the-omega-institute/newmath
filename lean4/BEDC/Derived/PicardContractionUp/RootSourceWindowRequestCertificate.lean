import BEDC.Derived.PicardContractionUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionRootSourceWindowPacket_request_row_certificate
    [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      request : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionRootSourceWindowPacket banach contraction lipschitz iterates modulus
        endpoint transport routes provenance name request bundle pkg ->
      PkgSig bundle request pkg ->
        SemanticNameCert
            (fun row : BHist => hsame row request ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row banach ∨ hsame row contraction ∨ hsame row lipschitz ∨
                hsame row iterates ∨ hsame row modulus ∨ hsame row endpoint ∨
                  hsame row transport ∨ hsame row routes ∨ hsame row provenance ∨
                    hsame row name ∨ hsame row request)
            (fun row : BHist => hsame row request ∧ PkgSig bundle request pkg)
            hsame ∧
          UnaryHistory request ∧ PkgSig bundle request pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro rootPacket requestPkg
  obtain ⟨_picardPacket, requestUnary⟩ := rootPacket
  have sourceRequest :
      (fun row : BHist => hsame row request ∧ UnaryHistory row) request := by
    exact ⟨hsame_refl request, requestUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row request ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row banach ∨ hsame row contraction ∨ hsame row lipschitz ∨
              hsame row iterates ∨ hsame row modulus ∨ hsame row endpoint ∨
                hsame row transport ∨ hsame row routes ∨ hsame row provenance ∨
                  hsame row name ∨ hsame row request)
          (fun row : BHist => hsame row request ∧ PkgSig bundle request pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro request sourceRequest
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
      exact ⟨source.left, requestPkg⟩
  }
  exact ⟨cert, requestUnary, requestPkg⟩

end BEDC.Derived.PicardContractionUp
