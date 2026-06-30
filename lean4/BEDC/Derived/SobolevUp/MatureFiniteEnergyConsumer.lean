import BEDC.Derived.SobolevUp

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_mature_finite_energy_consumer [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert energyRead
      weakRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg →
      Cont magnitude gradient energyRead →
        Cont energyRead provenance weakRead →
          Cont weakRead localCert completionRead →
            PkgSig bundle completionRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row domain ∨ hsame row base ∨ hsame row codomain ∨
                      hsame row magnitude ∨ hsame row gradient ∨ hsame row energyRead ∨
                        hsame row weakRead ∨ hsame row completionRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont magnitude gradient energyRead ∧
                      Cont energyRead provenance weakRead ∧
                        Cont weakRead localCert completionRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle completionRead pkg)
                  hsame ∧
                UnaryHistory energyRead ∧ UnaryHistory weakRead ∧
                  UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: SobolevCarrier BHist hsame Cont ProbeBundle Pkg SemanticNameCert
  intro carrier magnitudeGradientEnergy energyProvenanceWeak weakLocalCompletion
    completionPkg
  obtain ⟨_domainUnary, _baseUnary, _codomainUnary, magnitudeUnary, gradientUnary,
    _transportsUnary, _routesUnary, provenanceUnary, localCertUnary, _domainBaseCodomain,
    _codomainMagnitudeGradient, _gradientTransportsRoutes, _routesProvenanceLocalCert,
    provenancePkg⟩ := carrier
  have energyUnary : UnaryHistory energyRead :=
    unary_cont_closed magnitudeUnary gradientUnary magnitudeGradientEnergy
  have weakUnary : UnaryHistory weakRead :=
    unary_cont_closed energyUnary provenanceUnary energyProvenanceWeak
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed weakUnary localCertUnary weakLocalCompletion
  have sourceCompletion :
      (fun row : BHist => hsame row completionRead ∧ UnaryHistory row) completionRead := by
    exact ⟨hsame_refl completionRead, completionUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row domain ∨ hsame row base ∨ hsame row codomain ∨
              hsame row magnitude ∨ hsame row gradient ∨ hsame row energyRead ∨
                hsame row weakRead ∨ hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont magnitude gradient energyRead ∧
              Cont energyRead provenance weakRead ∧
                Cont weakRead localCert completionRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle completionRead pkg)
          hsame := {
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, magnitudeGradientEnergy, energyProvenanceWeak, weakLocalCompletion,
          provenancePkg, completionPkg⟩
  }
  exact ⟨cert, energyUnary, weakUnary, completionUnary⟩

end BEDC.Derived.SobolevUp
