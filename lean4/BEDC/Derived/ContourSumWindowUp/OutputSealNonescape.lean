import BEDC.Derived.ContourSumWindowUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ContourSumWindowUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContourSumWindowCarrier_output_seal_nonescape [AskSetup] [PackageSetup]
    {contour holomorphic subdivision riemann output provenance outputSeal publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory contour ->
      UnaryHistory holomorphic ->
        UnaryHistory subdivision ->
          UnaryHistory riemann ->
            UnaryHistory output ->
              UnaryHistory provenance ->
                Cont contour holomorphic subdivision ->
                  Cont riemann output outputSeal ->
                    Cont outputSeal provenance publicRead ->
                      PkgSig bundle publicRead pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row contour ∨ hsame row holomorphic ∨
                                hsame row subdivision ∨ hsame row riemann ∨
                                  hsame row output ∨ hsame row outputSeal ∨
                                    hsame row publicRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont riemann output outputSeal ∧
                                Cont outputSeal provenance publicRead ∧
                                  PkgSig bundle publicRead pkg)
                            hsame ∧ UnaryHistory outputSeal ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro _contourUnary _holomorphicUnary _subdivisionUnary riemannUnary outputUnary
    provenanceUnary _subdivisionRoute outputSealRoute publicRoute publicPkg
  have outputSealUnary : UnaryHistory outputSeal :=
    unary_cont_closed riemannUnary outputUnary outputSealRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed outputSealUnary provenanceUnary publicRoute
  have sourceAtPublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead :=
    ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row contour ∨ hsame row holomorphic ∨ hsame row subdivision ∨
              hsame row riemann ∨ hsame row output ∨ hsame row outputSeal ∨
                hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont riemann output outputSeal ∧
              Cont outputSeal provenance publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourceAtPublic
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, outputSealRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, outputSealUnary, publicUnary⟩

end BEDC.Derived.ContourSumWindowUp
