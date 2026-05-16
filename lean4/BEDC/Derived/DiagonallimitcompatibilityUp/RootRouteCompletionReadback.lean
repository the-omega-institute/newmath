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

theorem DiagonalLimitCompatibilityRootRouteCompletionReadback [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance
      cert completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont readback realSeal completionRead →
        PkgSig bundle completionRead pkg →
          SemanticNameCert
            (fun row : BHist =>
              DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback
                realSeal transport route provenance cert bundle pkg ∧
                  (hsame row readback ∨ hsame row route ∨ hsame row completionRead))
            (fun row : BHist =>
              Cont dyadic windows readback ∧ Cont readback realSeal completionRead ∧
                Cont route cert transport ∧
                  (hsame row readback ∨ hsame row route ∨ hsame row completionRead))
            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier readbackRealSealCompletionRead _completionReadPkg
  have carrierWitness := carrier
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, _windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, dyadicWindowsReadback, _readbackRealSealRoute,
    routeCertTransport, provenancePkg⟩ := carrier
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealCompletionRead
  exact {
    core := {
      carrier_inhabited := Exists.intro readback
        ⟨carrierWitness, Or.inl (hsame_refl readback)⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other same source
        refine ⟨source.left, ?_⟩
        cases source.right with
        | inl rowReadback =>
            exact Or.inl (hsame_trans (hsame_symm same) rowReadback)
        | inr tail =>
            cases tail with
            | inl rowRoute =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm same) rowRoute))
            | inr rowCompletionRead =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm same) rowCompletionRead))
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨dyadicWindowsReadback, readbackRealSealCompletionRead, routeCertTransport,
          source.right⟩
    ledger_sound := by
      intro row source
      cases source.right with
      | inl rowReadback =>
          exact ⟨unary_transport readbackUnary (hsame_symm rowReadback), provenancePkg⟩
      | inr tail =>
          cases tail with
          | inl rowRoute =>
              exact ⟨unary_transport routeUnary (hsame_symm rowRoute), provenancePkg⟩
          | inr rowCompletionRead =>
              exact
                ⟨unary_transport completionReadUnary (hsame_symm rowCompletionRead),
                  provenancePkg⟩
  }

end BEDC.Derived.DiagonallimitcompatibilityUp
