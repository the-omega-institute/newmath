import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalRootDisplayPacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name display : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      hsame display
        (append typed
          (append fuel
            (append terminal
              (append normal
                (append continuation
                  (append transports (append routes (append provenance name)))))))) ->
        SemanticNameCert
            (fun row : BHist => hsame row display ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨
                hsame row normal ∨ hsame row continuation ∨ hsame row transports ∨
                  hsame row routes ∨ hsame row provenance ∨ hsame row name ∨
                    hsame row display)
            (fun row : BHist => hsame row display ∧ PkgSig bundle provenance pkg)
            hsame ∧
          UnaryHistory display := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro packet displaySame
  obtain ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
    transportsUnary, routesUnary, provenanceUnary, nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have packetUnary :
      UnaryHistory
        (append typed
          (append fuel
            (append terminal
              (append normal
                (append continuation
                  (append transports (append routes (append provenance name)))))))) := by
    exact
      unary_append_closed typedUnary
        (unary_append_closed fuelUnary
          (unary_append_closed terminalUnary
            (unary_append_closed normalUnary
              (unary_append_closed continuationUnary
                (unary_append_closed transportsUnary
                  (unary_append_closed routesUnary
                    (unary_append_closed provenanceUnary nameUnary)))))))
  have displayUnary : UnaryHistory display :=
    unary_transport packetUnary (hsame_symm displaySame)
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row display ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨
              hsame row normal ∨ hsame row continuation ∨ hsame row transports ∨
                hsame row routes ∨ hsame row provenance ∨ hsame row name ∨
                  hsame row display)
          (fun row : BHist => hsame row display ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro display ⟨hsame_refl display, displayUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg⟩
  }
  exact ⟨cert, displayUnary⟩

end BEDC.Derived.ZnormalUp
