import BEDC.Derived.LipschitzMapUp

namespace BEDC.Derived.LipschitzMapUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LipschitzMapCarrier_completemetric_regular_seal_boundary [AskSetup] [PackageSetup]
    {source target bound graph modulus transports routes provenance localCert realSeal
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LipschitzMapCarrier source target bound graph modulus transports routes provenance localCert
        bundle pkg ->
      Cont modulus routes realSeal ->
        Cont realSeal provenance completionRead ->
          PkgSig bundle realSeal pkg ->
            PkgSig bundle completionRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row modulus ∨ hsame row realSeal ∨ hsame row completionRead)
                  (fun row : BHist =>
                    hsame row completionRead ∧ PkgSig bundle completionRead pkg)
                  hsame ∧
                UnaryHistory modulus ∧ UnaryHistory realSeal ∧ UnaryHistory completionRead ∧
                  Cont graph bound modulus ∧ Cont modulus routes realSeal ∧
                    Cont realSeal provenance completionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro carrier modulusRoutesRealSeal realSealProvenanceCompletion _realSealPkg completionPkg
  obtain ⟨_sourceUnary, _targetUnary, boundUnary, graphUnary, _transportsUnary, routesUnary,
    _localCertUnary, graphBoundModulus, modulusRoutesProvenance, _provenancePkg⟩ := carrier
  have modulusUnary : UnaryHistory modulus :=
    unary_cont_closed graphUnary boundUnary graphBoundModulus
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed modulusUnary routesUnary modulusRoutesProvenance
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed modulusUnary routesUnary modulusRoutesRealSeal
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed realSealUnary provenanceUnary realSealProvenanceCompletion
  have sourceCompletion :
      (fun row : BHist => hsame row completionRead ∧ UnaryHistory row) completionRead := by
    exact ⟨hsame_refl completionRead, completionUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row modulus ∨ hsame row realSeal ∨ hsame row completionRead)
        (fun row : BHist => hsame row completionRead ∧ PkgSig bundle completionRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro completionRead sourceCompletion
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
        exact Or.inr (Or.inr source.left)
      ledger_sound := by
        intro _row source
        exact ⟨source.left, completionPkg⟩
    }
  exact
    ⟨cert, modulusUnary, realSealUnary, completionUnary, graphBoundModulus,
      modulusRoutesRealSeal, realSealProvenanceCompletion⟩

end BEDC.Derived.LipschitzMapUp
