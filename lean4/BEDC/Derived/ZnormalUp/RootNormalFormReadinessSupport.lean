import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_normal_form_readiness_support_totality [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name normalRead
      readiness : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont normal continuation normalRead ->
        Cont normalRead routes readiness ->
          PkgSig bundle readiness pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row readiness ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨
                    hsame row normal ∨ hsame row normalRead ∨ hsame row readiness)
                (fun row : BHist => hsame row readiness ∧ PkgSig bundle readiness pkg)
                hsame ∧
              UnaryHistory normalRead ∧ UnaryHistory readiness := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet normalContinuationRead normalReadRoutesReadiness readinessPkg
  obtain ⟨_typedUnary, _fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, _provenancePkg⟩ :=
    packet
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationRead
  have readinessUnary : UnaryHistory readiness :=
    unary_cont_closed normalReadUnary routesUnary normalReadRoutesReadiness
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readiness ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨
              hsame row normal ∨ hsame row normalRead ∨ hsame row readiness)
          (fun row : BHist => hsame row readiness ∧ PkgSig bundle readiness pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro readiness ⟨hsame_refl readiness, readinessUnary⟩
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
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, readinessPkg⟩
    }
  exact ⟨cert, normalReadUnary, readinessUnary⟩

end BEDC.Derived.ZnormalUp
