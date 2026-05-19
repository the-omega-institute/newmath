import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_downstream_normal_consumer_nonescape [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name normalRead downstream
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont normal continuation normalRead →
        Cont normalRead transports downstream →
          Cont downstream routes consumer →
            PkgSig bundle consumer pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row normal ∨ hsame row continuation ∨ hsame row normalRead ∨
                      hsame row downstream ∨ hsame row consumer)
                  (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
                  hsame ∧
                UnaryHistory normalRead ∧ UnaryHistory downstream ∧ UnaryHistory consumer ∧
                  PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet normalContinuationRead normalReadTransportsDownstream downstreamRoutesConsumer
    consumerPkg
  obtain ⟨_typedUnary, _fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    transportsUnary, routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationRead
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed normalReadUnary transportsUnary normalReadTransportsDownstream
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed downstreamUnary routesUnary downstreamRoutesConsumer
  have consumerSource :
      (fun row : BHist => hsame row consumer ∧ UnaryHistory row) consumer := by
    exact ⟨hsame_refl consumer, consumerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row normal ∨ hsame row continuation ∨ hsame row normalRead ∨
              hsame row downstream ∨ hsame row consumer)
          (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro consumer consumerSource
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
          intro row row' sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro row source
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro row source
        exact ⟨source.left, consumerPkg⟩
    }
  exact ⟨cert, normalReadUnary, downstreamUnary, consumerUnary, provenancePkg⟩

end BEDC.Derived.ZnormalUp
