import BEDC.Derived.DyadicRoundingWindowUp

namespace BEDC.Derived.DyadicRoundingWindowUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicRoundingWindowCarrier_bridge_facing_handoff [AskSetup] [PackageSetup]
    {stream precision endpoint readback regular realSeal transport route provenance localName
      consumerRead standardRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicRoundingWindowCarrier stream precision endpoint readback regular realSeal transport route
        provenance localName bundle pkg ->
      Cont realSeal provenance consumerRead ->
        Cont consumerRead provenance standardRead ->
          PkgSig bundle consumerRead pkg ->
            PkgSig bundle standardRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row standardRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row stream ∨ hsame row precision ∨ hsame row endpoint ∨
                      hsame row readback ∨ hsame row regular ∨ hsame row realSeal ∨
                        hsame row consumerRead ∨ hsame row standardRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont realSeal provenance consumerRead ∧
                      Cont consumerRead provenance standardRead ∧
                        PkgSig bundle consumerRead pkg ∧ PkgSig bundle standardRead pkg)
                  hsame ∧ UnaryHistory standardRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier realSealConsumerRoute consumerStandardRoute consumerPkg standardPkg
  obtain
    ⟨streamUnary, _precisionUnary, _endpointUnary, _readbackUnary, _regularUnary,
      realSealUnary, _precisionStreamEndpoint, _streamEndpointReadback,
      _readbackRegularRealSeal, _provenancePkg, localNameStream,
      localNameProvenance⟩ := carrier
  have streamProvenance : hsame stream provenance :=
    hsame_trans (hsame_symm localNameStream) localNameProvenance
  have provenanceUnary : UnaryHistory provenance :=
    unary_transport streamUnary streamProvenance
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed realSealUnary provenanceUnary realSealConsumerRoute
  have standardUnary : UnaryHistory standardRead :=
    unary_cont_closed consumerUnary provenanceUnary consumerStandardRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row standardRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream ∨ hsame row precision ∨ hsame row endpoint ∨
              hsame row readback ∨ hsame row regular ∨ hsame row realSeal ∨
                hsame row consumerRead ∨ hsame row standardRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont realSeal provenance consumerRead ∧
              Cont consumerRead provenance standardRead ∧ PkgSig bundle consumerRead pkg ∧
                PkgSig bundle standardRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro standardRead ⟨hsame_refl standardRead, standardUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, realSealConsumerRoute, consumerStandardRoute, consumerPkg,
          standardPkg⟩
  }
  exact ⟨cert, standardUnary⟩

end BEDC.Derived.DyadicRoundingWindowUp
