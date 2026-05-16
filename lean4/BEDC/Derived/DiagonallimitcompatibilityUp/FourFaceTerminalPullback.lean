import BEDC.Derived.DiagonallimitcompatibilityUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_four_face_terminal_pullback [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector rootPullback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal windows selector →
        Cont selector readback rootPullback →
          PkgSig bundle rootPullback pkg →
            SemanticNameCert
              (fun row : BHist =>
                DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows
                  readback realSeal transport route provenance cert bundle pkg ∧
                    hsame row rootPullback)
              (fun row : BHist =>
                Cont diagonal windows selector ∧ Cont selector readback row ∧
                  PkgSig bundle rootPullback pkg)
              (fun row : BHist => UnaryHistory row ∧ PkgSig bundle rootPullback pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro carrier diagonalWindowsSelector selectorReadbackPullback pullbackPkg
  rcases carrier with
    ⟨diagonalUnary, triangleUnary, sealUnary, dyadicUnary, windowsUnary, readbackUnary,
      realSealUnary, transportUnary, routeUnary, provenanceUnary, certUnary,
      diagonalTriangleSeal, dyadicWindowsReadback, readbackRealSealRoute,
      routeCertTransport, provenancePkg⟩
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have pullbackUnary : UnaryHistory rootPullback :=
    unary_cont_closed selectorUnary readbackUnary selectorReadbackPullback
  have carrierWitness :
      DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback
        realSeal transport route provenance cert bundle pkg :=
    ⟨diagonalUnary, triangleUnary, sealUnary, dyadicUnary, windowsUnary, readbackUnary,
      realSealUnary, transportUnary, routeUnary, provenanceUnary, certUnary,
      diagonalTriangleSeal, dyadicWindowsReadback, readbackRealSealRoute, routeCertTransport,
      provenancePkg⟩
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro rootPullback
          (And.intro carrierWitness (hsame_refl rootPullback))
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨diagonalWindowsSelector,
          cont_result_hsame_transport selectorReadbackPullback (hsame_symm source.right),
          pullbackPkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport pullbackUnary (hsame_symm source.right), pullbackPkg⟩
  }

end BEDC.Derived.DiagonallimitcompatibilityUp
