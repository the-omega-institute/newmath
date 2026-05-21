import BEDC.Derived.PicardContractionUp

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionPacket_root_consumer_triad_exhaustion
    [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      odeRead newtonRead regseqRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg →
      Cont iterates endpoint odeRead →
        Cont endpoint transport newtonRead →
          Cont iterates modulus regseqRead →
            Cont endpoint transport realRead →
              PkgSig bundle odeRead pkg →
                PkgSig bundle newtonRead pkg →
                  PkgSig bundle regseqRead pkg →
                    PkgSig bundle realRead pkg →
                      SemanticNameCert
                        (fun row : BHist =>
                          hsame row iterates ∨ hsame row modulus ∨ hsame row endpoint ∨
                            hsame row odeRead ∨ hsame row newtonRead ∨
                              hsame row regseqRead ∨ hsame row realRead)
                        (fun row : BHist => UnaryHistory row)
                        (fun _row : BHist =>
                          PkgSig bundle name pkg ∧ PkgSig bundle odeRead pkg ∧
                            PkgSig bundle newtonRead pkg ∧ PkgSig bundle regseqRead pkg ∧
                              PkgSig bundle realRead pkg)
                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro packet iteratesEndpointOdeRead endpointTransportNewtonRead iteratesModulusRegseqRead
    endpointTransportRealRead odeReadPkg newtonReadPkg regseqReadPkg realReadPkg
  obtain ⟨_banachUnary, _contractionUnary, _lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _banachContractionLipschitz, _iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have odeReadUnary : UnaryHistory odeRead :=
    unary_cont_closed iteratesUnary endpointUnary iteratesEndpointOdeRead
  have newtonReadUnary : UnaryHistory newtonRead :=
    unary_cont_closed endpointUnary transportUnary endpointTransportNewtonRead
  have regseqReadUnary : UnaryHistory regseqRead :=
    unary_cont_closed iteratesUnary modulusUnary iteratesModulusRegseqRead
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed endpointUnary transportUnary endpointTransportRealRead
  exact {
    core := {
      carrier_inhabited := Exists.intro iterates (Or.inl (hsame_refl iterates))
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
        intro _row _row' sameRows sourceRow
        cases sourceRow with
        | inl sameIterates =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameIterates)
        | inr rest =>
            cases rest with
            | inl sameModulus =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameModulus))
            | inr rest =>
                cases rest with
                | inl sameEndpoint =>
                    exact
                      Or.inr
                        (Or.inr
                          (Or.inl (hsame_trans (hsame_symm sameRows) sameEndpoint)))
                | inr rest =>
                    cases rest with
                    | inl sameOdeRead =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inl (hsame_trans (hsame_symm sameRows) sameOdeRead))))
                    | inr rest =>
                        cases rest with
                        | inl sameNewtonRead =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl
                                        (hsame_trans (hsame_symm sameRows)
                                          sameNewtonRead)))))
                        | inr rest =>
                            cases rest with
                            | inl sameRegseqRead =>
                                exact
                                  Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inl
                                              (hsame_trans (hsame_symm sameRows)
                                                sameRegseqRead))))))
                            | inr sameRealRead =>
                                exact
                                  Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (hsame_trans (hsame_symm sameRows)
                                                sameRealRead))))))
    }
    pattern_sound := by
      intro _row sourceRow
      cases sourceRow with
      | inl sameIterates =>
          exact unary_transport iteratesUnary (hsame_symm sameIterates)
      | inr rest =>
          cases rest with
          | inl sameModulus =>
              exact unary_transport modulusUnary (hsame_symm sameModulus)
          | inr rest =>
              cases rest with
              | inl sameEndpoint =>
                  exact unary_transport endpointUnary (hsame_symm sameEndpoint)
              | inr rest =>
                  cases rest with
                  | inl sameOdeRead =>
                      exact unary_transport odeReadUnary (hsame_symm sameOdeRead)
                  | inr rest =>
                      cases rest with
                      | inl sameNewtonRead =>
                          exact unary_transport newtonReadUnary (hsame_symm sameNewtonRead)
                      | inr rest =>
                          cases rest with
                          | inl sameRegseqRead =>
                              exact unary_transport regseqReadUnary (hsame_symm sameRegseqRead)
                          | inr sameRealRead =>
                              exact unary_transport realReadUnary (hsame_symm sameRealRead)
    ledger_sound := by
      intro _row _sourceRow
      exact ⟨namePkg, odeReadPkg, newtonReadPkg, regseqReadPkg, realReadPkg⟩
  }

end BEDC.Derived.PicardContractionUp
