import BEDC.Derived.SobolevUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_completion_facing_root_scope [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert
      rootRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg ->
      Cont domain base rootRead ->
        Cont rootRead gradient completionRead ->
          PkgSig bundle completionRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row domain ∨ hsame row base ∨ hsame row codomain ∨
                    hsame row magnitude ∨ hsame row gradient ∨ hsame row transports ∨
                      hsame row routes ∨ hsame row provenance ∨ hsame row localCert ∨
                        hsame row completionRead)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle completionRead pkg ∧
                    hsame row completionRead)
                hsame ∧
              UnaryHistory rootRead ∧ UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: SobolevCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier rootRoute completionRoute completionPkg
  obtain ⟨domainUnary, baseUnary, _codomainUnary, _magnitudeUnary, gradientUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary, _domainBaseCodomain,
    _codomainMagnitudeGradient, _gradientTransportsRoutes, _routesProvenanceLocalCert,
    provenancePkg⟩ := carrier
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed domainUnary baseUnary rootRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed rootReadUnary gradientUnary completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row domain ∨ hsame row base ∨ hsame row codomain ∨
              hsame row magnitude ∨ hsame row gradient ∨ hsame row transports ∨
                hsame row routes ∨ hsame row provenance ∨ hsame row localCert ∨
                  hsame row completionRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle completionRead pkg ∧
              hsame row completionRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead ⟨hsame_refl completionRead, completionReadUnary⟩
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
      exact ⟨provenancePkg, completionPkg, source.left⟩
  }
  exact ⟨cert, rootReadUnary, completionReadUnary⟩

end BEDC.Derived.SobolevUp
