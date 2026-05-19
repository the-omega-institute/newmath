import BEDC.Derived.PicardContractionUp

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionPacket_finite_consumer_exhaustion [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      odeConsumer realConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg →
      Cont iterates endpoint odeConsumer →
        Cont modulus endpoint realConsumer →
          PkgSig bundle odeConsumer pkg →
            PkgSig bundle realConsumer pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row odeConsumer ∨ hsame row realConsumer)
                  (fun _row : BHist =>
                    Cont iterates endpoint odeConsumer ∧ Cont modulus endpoint realConsumer)
                  (fun row : BHist =>
                    UnaryHistory row ∧
                      (PkgSig bundle odeConsumer pkg ∨ PkgSig bundle realConsumer pkg))
                  hsame ∧
                UnaryHistory odeConsumer ∧ UnaryHistory realConsumer := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet iteratesEndpointOdeConsumer modulusEndpointRealConsumer odeConsumerPkg
    realConsumerPkg
  obtain ⟨_banachUnary, _contractionUnary, _lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _banachContractionLipschitz, _iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, _namePkg⟩ := packet
  have odeConsumerUnary : UnaryHistory odeConsumer :=
    unary_cont_closed iteratesUnary endpointUnary iteratesEndpointOdeConsumer
  have realConsumerUnary : UnaryHistory realConsumer :=
    unary_cont_closed modulusUnary endpointUnary modulusEndpointRealConsumer
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row odeConsumer ∨ hsame row realConsumer)
          (fun _row : BHist =>
            Cont iterates endpoint odeConsumer ∧ Cont modulus endpoint realConsumer)
          (fun row : BHist =>
            UnaryHistory row ∧
              (PkgSig bundle odeConsumer pkg ∨ PkgSig bundle realConsumer pkg))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro odeConsumer (Or.inl (hsame_refl odeConsumer))
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
        intro row row' sameRows sourceRow
        cases sourceRow with
        | inl sameOde =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameOde)
        | inr sameReal =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) sameReal)
    }
    pattern_sound := by
      intro _row _sourceRow
      exact ⟨iteratesEndpointOdeConsumer, modulusEndpointRealConsumer⟩
    ledger_sound := by
      intro row sourceRow
      cases sourceRow with
      | inl sameOde =>
          exact
            ⟨unary_transport odeConsumerUnary (hsame_symm sameOde),
              Or.inl odeConsumerPkg⟩
      | inr sameReal =>
          exact
            ⟨unary_transport realConsumerUnary (hsame_symm sameReal),
              Or.inr realConsumerPkg⟩
  }
  exact ⟨cert, odeConsumerUnary, realConsumerUnary⟩

end BEDC.Derived.PicardContractionUp
