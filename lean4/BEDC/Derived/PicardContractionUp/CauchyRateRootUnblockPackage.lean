import BEDC.Derived.PicardContractionUp

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionPacket_cauchyrate_root_unblock_package [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      rateSource realSeal odeRead newtonRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg →
      Cont iterates modulus rateSource →
        Cont rateSource endpoint realSeal →
          Cont iterates endpoint odeRead →
            Cont endpoint transport newtonRead →
              PkgSig bundle rateSource pkg →
                PkgSig bundle realSeal pkg →
                  PkgSig bundle odeRead pkg →
                    PkgSig bundle newtonRead pkg →
                      SemanticNameCert
                          (fun row : BHist =>
                            hsame row rateSource ∨ hsame row realSeal ∨ hsame row odeRead ∨
                              hsame row newtonRead)
                          (fun _row : BHist =>
                            Cont iterates modulus rateSource ∧
                              Cont rateSource endpoint realSeal ∧
                                Cont iterates endpoint odeRead ∧
                                  Cont endpoint transport newtonRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧
                              (PkgSig bundle rateSource pkg ∨ PkgSig bundle realSeal pkg ∨
                                PkgSig bundle odeRead pkg ∨ PkgSig bundle newtonRead pkg))
                          hsame ∧
                        UnaryHistory rateSource ∧ UnaryHistory realSeal ∧
                          UnaryHistory odeRead ∧ UnaryHistory newtonRead ∧
                            PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet iteratesModulusRate rateEndpointReal iteratesEndpointOde
    endpointTransportNewton ratePkg realPkg odePkg newtonPkg
  obtain ⟨_banachUnary, _contractionUnary, _lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _banachContractionLipschitz, _iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have rateUnary : UnaryHistory rateSource :=
    unary_cont_closed iteratesUnary modulusUnary iteratesModulusRate
  have realUnary : UnaryHistory realSeal :=
    unary_cont_closed rateUnary endpointUnary rateEndpointReal
  have odeUnary : UnaryHistory odeRead :=
    unary_cont_closed iteratesUnary endpointUnary iteratesEndpointOde
  have newtonUnary : UnaryHistory newtonRead :=
    unary_cont_closed endpointUnary transportUnary endpointTransportNewton
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row rateSource ∨ hsame row realSeal ∨ hsame row odeRead ∨
              hsame row newtonRead)
          (fun _row : BHist =>
            Cont iterates modulus rateSource ∧ Cont rateSource endpoint realSeal ∧
              Cont iterates endpoint odeRead ∧ Cont endpoint transport newtonRead)
          (fun row : BHist =>
            UnaryHistory row ∧
              (PkgSig bundle rateSource pkg ∨ PkgSig bundle realSeal pkg ∨
                PkgSig bundle odeRead pkg ∨ PkgSig bundle newtonRead pkg))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rateSource (Or.inl (hsame_refl rateSource))
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
        | inl sameRate =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameRate)
        | inr tail =>
            cases tail with
            | inl sameReal =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameReal))
            | inr tail' =>
                cases tail' with
                | inl sameOde =>
                    exact Or.inr
                      (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameOde)))
                | inr sameNewton =>
                    exact Or.inr
                      (Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameNewton)))
    }
    pattern_sound := by
      intro _row _sourceRow
      exact
        ⟨iteratesModulusRate, rateEndpointReal, iteratesEndpointOde,
          endpointTransportNewton⟩
    ledger_sound := by
      intro row sourceRow
      cases sourceRow with
      | inl sameRate =>
          exact
            ⟨unary_transport rateUnary (hsame_symm sameRate), Or.inl ratePkg⟩
      | inr tail =>
          cases tail with
          | inl sameReal =>
              exact
                ⟨unary_transport realUnary (hsame_symm sameReal),
                  Or.inr (Or.inl realPkg)⟩
          | inr tail' =>
              cases tail' with
              | inl sameOde =>
                  exact
                    ⟨unary_transport odeUnary (hsame_symm sameOde),
                      Or.inr (Or.inr (Or.inl odePkg))⟩
              | inr sameNewton =>
                  exact
                    ⟨unary_transport newtonUnary (hsame_symm sameNewton),
                      Or.inr (Or.inr (Or.inr newtonPkg))⟩
  }
  exact ⟨cert, rateUnary, realUnary, odeUnary, newtonUnary, namePkg⟩

end BEDC.Derived.PicardContractionUp
