import BEDC.Derived.SobolevUp

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_hilbert_norm_readback_scope [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert normRead
      hilbertRead readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg ->
      Cont codomain magnitude normRead ->
        Cont base codomain hilbertRead ->
          Cont normRead gradient readback ->
            PkgSig bundle readback pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row readback ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row domain ∨ hsame row base ∨ hsame row codomain ∨
                      hsame row magnitude ∨ hsame row gradient ∨ hsame row normRead ∨
                        hsame row hilbertRead ∨ hsame row readback)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle readback pkg)
                  hsame ∧
                UnaryHistory normRead ∧ UnaryHistory hilbertRead ∧
                  UnaryHistory readback ∧ hsame readback (append normRead gradient) ∧
                    Cont domain base codomain ∧ Cont codomain magnitude gradient ∧
                      Cont base codomain hilbertRead ∧ Cont normRead gradient readback := by
  -- BEDC touchpoint anchor: SobolevCarrier BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier codomainMagnitudeNorm baseCodomainHilbert normGradientReadback readbackPkg
  obtain ⟨domainUnary, baseUnary, codomainUnary, magnitudeUnary, gradientUnary,
    _transportsUnary, _routesUnary, provenanceUnary, _localCertUnary, domainBaseCodomain,
    codomainMagnitudeGradient, _gradientTransportsRoutes, _routesProvenanceLocalCert,
    provenancePkg⟩ := carrier
  have normUnary : UnaryHistory normRead :=
    unary_cont_closed codomainUnary magnitudeUnary codomainMagnitudeNorm
  have hilbertUnary : UnaryHistory hilbertRead :=
    unary_cont_closed baseUnary codomainUnary baseCodomainHilbert
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed normUnary gradientUnary normGradientReadback
  have readbackAppend : hsame readback (append normRead gradient) := by
    exact normGradientReadback
  have sourceReadback :
      (fun row : BHist => hsame row readback ∧ UnaryHistory row) readback := by
    exact ⟨hsame_refl readback, readbackUnary⟩
  have core :
      NameCert (fun row : BHist => hsame row readback ∧ UnaryHistory row) hsame := by
    exact {
      carrier_inhabited := Exists.intro readback sourceReadback
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other sameRows sourceRow
        have sameOtherReadback : hsame other readback :=
          hsame_trans (hsame_symm sameRows) sourceRow.left
        have otherUnary : UnaryHistory other :=
          unary_transport sourceRow.right sameRows
        exact ⟨sameOtherReadback, otherUnary⟩
    }
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readback ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row domain ∨ hsame row base ∨ hsame row codomain ∨ hsame row magnitude ∨
              hsame row gradient ∨ hsame row normRead ∨ hsame row hilbertRead ∨
                hsame row readback)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle readback pkg)
          hsame := by
    exact {
      core := core
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.right, provenancePkg, readbackPkg⟩
    }
  exact
    ⟨cert, normUnary, hilbertUnary, readbackUnary, readbackAppend, domainBaseCodomain,
      codomainMagnitudeGradient, baseCodomainHilbert, normGradientReadback⟩

end BEDC.Derived.SobolevUp
