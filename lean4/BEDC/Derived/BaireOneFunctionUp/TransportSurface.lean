import BEDC.Derived.BaireOneFunctionUp

namespace BEDC.Derived.BaireOneFunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireOneFunctionCarrier_namecert_obligations_transport_surface
    [AskSetup] [PackageSetup]
    {X F S Q R L H C P N endpoint transportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg →
      Cont S Q endpoint →
        Cont R L transportRead →
          PkgSig bundle endpoint pkg →
            PkgSig bundle transportRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row endpoint ∨ hsame row transportRead) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨
                      hsame row R ∨ hsame row L ∨ hsame row H ∨ hsame row C ∨
                        hsame row P ∨ hsame row N ∨ hsame row endpoint ∨
                          hsame row transportRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont S Q endpoint ∧ Cont R L transportRead ∧
                      PkgSig bundle endpoint pkg ∧ PkgSig bundle transportRead pkg)
                  hsame ∧
                UnaryHistory endpoint ∧ UnaryHistory transportRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier endpointRoute transportRoute endpointPkg transportPkg
  obtain ⟨_xUnary, _fUnary, sUnary, qUnary, rUnary, lUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _sourceApproxSchedule, _scheduleReadbackReal,
    _realHandoffTransport, _transportContinuationProvenance, _provenancePkg,
    _namePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed sUnary qUnary endpointRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed rUnary lUnary transportRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row endpoint ∨ hsame row transportRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨ hsame row R ∨
              hsame row L ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row endpoint ∨ hsame row transportRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S Q endpoint ∧ Cont R L transportRead ∧
              PkgSig bundle endpoint pkg ∧ PkgSig bundle transportRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint ⟨Or.inl (hsame_refl endpoint), endpointUnary⟩
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
        constructor
        · cases source.left with
          | inl sameEndpoint =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameEndpoint)
          | inr sameTransport =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameTransport)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameEndpoint =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (Or.inl sameEndpoint))))))))))
      | inr sameTransport =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (Or.inr sameTransport))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, endpointRoute, transportRoute, endpointPkg, transportPkg⟩
  }
  exact ⟨cert, endpointUnary, transportUnary⟩

theorem BaireOneFunctionCarrier_pointwise_limit_handoff_certificate
    [AskSetup] [PackageSetup]
    {X F S Q R L H C P N pointwiseRead lscRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg →
      Cont S Q pointwiseRead →
        PkgSig bundle pointwiseRead pkg →
          Cont R L lscRead →
            PkgSig bundle lscRead pkg →
              hsame pointwiseRead R ∧ UnaryHistory pointwiseRead ∧
                UnaryHistory lscRead ∧ Cont S Q pointwiseRead ∧ Cont R L lscRead ∧
                  PkgSig bundle pointwiseRead pkg ∧ PkgSig bundle lscRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame UnaryHistory
  intro carrier pointwiseRoute pointwisePkg lscRoute lscPkg
  obtain ⟨_xUnary, _fUnary, _sUnary, _qUnary, rUnary, lUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _sourceApproxSchedule, scheduleReadbackReal,
    _realHandoffTransport, _transportContinuationProvenance, _provenancePkg,
    _namePkg⟩ := carrier
  have pointwiseReal : hsame pointwiseRead R :=
    cont_deterministic pointwiseRoute scheduleReadbackReal
  have pointwiseUnary : UnaryHistory pointwiseRead :=
    unary_transport rUnary (hsame_symm pointwiseReal)
  have lscUnary : UnaryHistory lscRead :=
    unary_cont_closed rUnary lUnary lscRoute
  exact
    ⟨pointwiseReal, pointwiseUnary, lscUnary, pointwiseRoute, lscRoute, pointwisePkg,
      lscPkg⟩

end BEDC.Derived.BaireOneFunctionUp
