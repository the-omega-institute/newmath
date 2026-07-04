import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BaireOneFunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BaireOneFunctionCarrier [AskSetup] [PackageSetup]
    (X F S Q R L H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory X ∧ UnaryHistory F ∧ UnaryHistory S ∧ UnaryHistory Q ∧
    UnaryHistory R ∧ UnaryHistory L ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont X F S ∧ Cont S Q R ∧
        Cont R L H ∧ Cont H C P ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem BaireOneFunctionCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {X F S Q R L H C P N endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg →
      Cont S Q endpoint →
        PkgSig bundle endpoint pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row endpoint ∧
                  BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg)
              (fun row : BHist =>
                hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨
                  hsame row R ∨ hsame row L ∨ hsame row H ∨ hsame row C ∨
                    hsame row P ∨ hsame row N ∨ hsame row endpoint)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle endpoint pkg)
              hsame ∧
            UnaryHistory endpoint := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier scheduleReadbackEndpoint endpointPkg
  have carrierWhole := carrier
  obtain ⟨_sourceUnary, _approximantsUnary, scheduleUnary, readbackUnary, _realUnary,
    _handoffUnary, _transportUnary, _continuationUnary, _provenanceUnary, _nameUnary,
    _sourceApproxSchedule, _scheduleReadbackReal, _realHandoffTransport,
    _transportContinuationProvenance, provenancePkg, _namePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed scheduleUnary readbackUnary scheduleReadbackEndpoint
  have sourceEndpoint :
      (fun row : BHist =>
        hsame row endpoint ∧
          BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg) endpoint := by
    exact ⟨hsame_refl endpoint, carrierWhole⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row endpoint ∧
              BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨ hsame row R ∨
              hsame row L ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row endpoint)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle endpoint pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint sourceEndpoint
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
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
                    (Or.inr
                      (Or.inr (Or.inr (Or.inr source.left)))))))))
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport endpointUnary (hsame_symm source.left), provenancePkg,
          endpointPkg⟩
  }
  exact ⟨cert, endpointUnary⟩

theorem BaireOneFunctionCarrier_pointwise_schedule_obligations [AskSetup] [PackageSetup]
    {X F S Q R L H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row H ∧ BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨ hsame row R ∨
              hsame row L ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame ∧
        UnaryHistory X ∧ UnaryHistory F ∧ UnaryHistory S ∧ UnaryHistory Q ∧
          UnaryHistory R ∧ UnaryHistory L ∧ UnaryHistory H ∧ UnaryHistory C ∧
            PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧ Cont X F S ∧
              Cont S Q R ∧ Cont R L H := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier
  have carrierWhole := carrier
  obtain ⟨xUnary, fUnary, sUnary, qUnary, rUnary, lUnary, hUnary, cUnary,
    _pUnary, _nUnary, sourceApproxSchedule, scheduleReadbackReal,
    realHandoffTransport, _transportContinuationProvenance, provenancePkg,
    namePkg⟩ := carrier
  have sourceTransport :
      (fun row : BHist =>
        hsame row H ∧ BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg)
          H := by
    exact ⟨hsame_refl H, carrierWhole⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row H ∧ BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨ hsame row R ∨
              hsame row L ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro H sourceTransport
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr (Or.inr (Or.inl source.left))))))
    ledger_sound := by
      intro row source
      exact ⟨unary_transport hUnary (hsame_symm source.left), provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, xUnary, fUnary, sUnary, qUnary, rUnary, lUnary, hUnary, cUnary,
      provenancePkg, namePkg, sourceApproxSchedule, scheduleReadbackReal,
      realHandoffTransport⟩

theorem BaireOneFunctionCarrier_pointwise_limit_ledger [AskSetup] [PackageSetup]
    {X F S Q R L H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row R ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨ hsame row R)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg ∧ Cont S Q R)
          hsame ∧
        UnaryHistory R ∧ Cont S Q R := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro carrier
  obtain ⟨_sourceUnary, _approximantsUnary, scheduleUnary, readbackUnary, _realUnary,
    _handoffUnary, _transportUnary, _continuationUnary, _provenanceUnary, _nameUnary,
    _sourceApproxSchedule, scheduleReadbackReal, _realHandoffTransport,
    _transportContinuationProvenance, provenancePkg, _namePkg⟩ := carrier
  have realUnary : UnaryHistory R :=
    unary_cont_closed scheduleUnary readbackUnary scheduleReadbackReal
  have sourceReal :
      (fun row : BHist => hsame row R ∧ UnaryHistory row) R := by
    exact ⟨hsame_refl R, realUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row R ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨ hsame row R)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg ∧ Cont S Q R)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro R sourceReal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, scheduleReadbackReal⟩
  }
  exact ⟨cert, realUnary, scheduleReadbackReal⟩

theorem BaireOneFunctionCarrier_lowersemicontinuous_handoff [AskSetup] [PackageSetup]
    {X F S Q R L H C P N lscRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg ->
      Cont R L lscRead ->
        PkgSig bundle lscRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row lscRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨
                  hsame row R ∨ hsame row L ∨ hsame row lscRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont R L lscRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle lscRead pkg)
              hsame ∧
            UnaryHistory lscRead ∧ Cont X F S ∧ Cont S Q R ∧
              PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier realHandoffRead lscPkg
  obtain ⟨sourceUnary, approximantsUnary, _scheduleUnary, _readbackUnary, realUnary,
    handoffUnary, _transportUnary, _continuationUnary, _provenanceUnary, _nameUnary,
    sourceApproxSchedule, scheduleReadbackReal, _realHandoffTransport,
    _transportContinuationProvenance, provenancePkg, _namePkg⟩ := carrier
  have lscUnary : UnaryHistory lscRead :=
    unary_cont_closed realUnary handoffUnary realHandoffRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row lscRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨ hsame row R ∨
              hsame row L ∨ hsame row lscRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R L lscRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle lscRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro lscRead ⟨hsame_refl lscRead, lscUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, realHandoffRead, provenancePkg, lscPkg⟩
  }
  exact ⟨cert, lscUnary, sourceApproxSchedule, scheduleReadbackReal, provenancePkg⟩

theorem BaireOneFunctionCarrier_public_export [AskSetup] [PackageSetup]
    {X F S Q R L H C P N publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg →
      Cont L C publicRead →
        PkgSig bundle publicRead pkg →
          UnaryHistory X ∧ UnaryHistory F ∧ UnaryHistory S ∧ UnaryHistory Q ∧
            UnaryHistory R ∧ UnaryHistory L ∧ UnaryHistory H ∧ UnaryHistory C ∧
              UnaryHistory publicRead ∧ Cont X F S ∧ Cont S Q R ∧ Cont R L H ∧
                Cont L C publicRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                  PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier publicRoute publicPkg
  obtain ⟨xUnary, fUnary, sUnary, qUnary, rUnary, lUnary, hUnary, cUnary,
    _pUnary, _nUnary, sourceApproxSchedule, scheduleReadbackReal,
    realHandoffTransport, _transportContinuationProvenance, provenancePkg,
    namePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed lUnary cUnary publicRoute
  exact
    ⟨xUnary, fUnary, sUnary, qUnary, rUnary, lUnary, hUnary, cUnary, publicUnary,
      sourceApproxSchedule, scheduleReadbackReal, realHandoffTransport, publicRoute,
      provenancePkg, namePkg, publicPkg⟩

theorem BaireOneFunctionCarrier_finite_schedule_nonescape [AskSetup] [PackageSetup]
    {X F S Q R L H C P N pointwiseRead lscRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg →
      Cont S Q pointwiseRead →
        Cont R L lscRead →
          Cont L C publicRead →
            PkgSig bundle publicRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row pointwiseRead ∨ hsame row lscRead ∨ hsame row publicRead) ∧
                      UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨
                      hsame row R ∨ hsame row L ∨ hsame row H ∨ hsame row C ∨
                        hsame row P ∨ hsame row N ∨ hsame row pointwiseRead ∨
                          hsame row lscRead ∨ hsame row publicRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont S Q pointwiseRead ∧ Cont R L lscRead ∧
                      Cont L C publicRead ∧ PkgSig bundle publicRead pkg)
                  hsame ∧ UnaryHistory pointwiseRead ∧ UnaryHistory lscRead ∧
                UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier pointwiseRoute lscRoute publicRoute publicPkg
  obtain ⟨_xUnary, _fUnary, sUnary, qUnary, rUnary, lUnary, _hUnary, cUnary,
    _pUnary, _nUnary, _sourceApproxSchedule, _scheduleReadbackReal,
    _realHandoffTransport, _transportContinuationProvenance, _provenancePkg,
    _namePkg⟩ := carrier
  have pointwiseUnary : UnaryHistory pointwiseRead :=
    unary_cont_closed sUnary qUnary pointwiseRoute
  have lscUnary : UnaryHistory lscRead :=
    unary_cont_closed rUnary lUnary lscRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed lUnary cUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row pointwiseRead ∨ hsame row lscRead ∨ hsame row publicRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨
              hsame row R ∨ hsame row L ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row pointwiseRead ∨ hsame row lscRead ∨
                  hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S Q pointwiseRead ∧ Cont R L lscRead ∧
              Cont L C publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro pointwiseRead
          ⟨Or.inl (hsame_refl pointwiseRead), pointwiseUnary⟩
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
        have lift : ∀ {target : BHist}, hsame _row target → hsame _other target := by
          intro _target sameTarget
          exact hsame_trans (hsame_symm sameRows) sameTarget
        constructor
        · cases source.left with
          | inl samePointwise =>
              exact Or.inl (lift samePointwise)
          | inr tail =>
              cases tail with
              | inl sameLsc =>
                  exact Or.inr (Or.inl (lift sameLsc))
              | inr samePublic =>
                  exact Or.inr (Or.inr (lift samePublic))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl samePointwise =>
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
                              (Or.inr (Or.inl samePointwise))))))))))
      | inr tail =>
          cases tail with
          | inl sameLsc =>
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
                                  (Or.inr (Or.inr (Or.inl sameLsc)))))))))))
          | inr samePublic =>
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
                                  (Or.inr (Or.inr (Or.inr samePublic)))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, pointwiseRoute, lscRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, pointwiseUnary, lscUnary, publicUnary⟩

theorem BaireOneFunctionCarrier_pointwise_readback_real_seal [AskSetup] [PackageSetup]
    {X F S Q R L H C P N pointwiseRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg ->
      Cont S Q pointwiseRead ->
        hsame pointwiseRead R ∧ UnaryHistory pointwiseRead ∧ Cont X F S ∧ Cont S Q R := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame UnaryHistory
  intro carrier pointwiseRoute
  obtain ⟨_xUnary, _fUnary, _sUnary, _qUnary, rUnary, _lUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, sourceApproxSchedule, scheduleReadbackReal, _realHandoffTransport,
    _transportContinuationProvenance, _provenancePkg, _namePkg⟩ := carrier
  have pointwiseReal : hsame pointwiseRead R :=
    cont_deterministic pointwiseRoute scheduleReadbackReal
  have pointwiseUnary : UnaryHistory pointwiseRead :=
    unary_transport rUnary (hsame_symm pointwiseReal)
  exact ⟨pointwiseReal, pointwiseUnary, sourceApproxSchedule, scheduleReadbackReal⟩

theorem BaireOneFunctionCarrier_finite_schedule_real_seal_nonescape
    [AskSetup] [PackageSetup]
    {X F S Q R L H C P N pointwiseRead lscRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg ->
      Cont S Q pointwiseRead ->
        Cont R L lscRead ->
          Cont L C publicRead ->
            PkgSig bundle publicRead pkg ->
              hsame pointwiseRead R ∧ UnaryHistory pointwiseRead ∧ UnaryHistory lscRead ∧
                UnaryHistory publicRead ∧ Cont R L lscRead ∧ Cont L C publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame UnaryHistory
  intro carrier pointwiseRoute lscRoute publicRoute _publicPkg
  obtain ⟨_xUnary, _fUnary, _sUnary, _qUnary, rUnary, lUnary, _hUnary, cUnary,
    _pUnary, _nUnary, _sourceApproxSchedule, scheduleReadbackReal, _realHandoffTransport,
    _transportContinuationProvenance, _provenancePkg, _namePkg⟩ := carrier
  have pointwiseReal : hsame pointwiseRead R :=
    cont_deterministic pointwiseRoute scheduleReadbackReal
  have pointwiseUnary : UnaryHistory pointwiseRead :=
    unary_transport rUnary (hsame_symm pointwiseReal)
  have lscUnary : UnaryHistory lscRead :=
    unary_cont_closed rUnary lUnary lscRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed lUnary cUnary publicRoute
  exact ⟨pointwiseReal, pointwiseUnary, lscUnary, publicUnary, lscRoute, publicRoute⟩

theorem BaireOneFunctionCarrier_pointwise_schedule_real_seal_route
    [AskSetup] [PackageSetup]
    {X F S Q R L H C P N pointwiseRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg ->
      Cont S Q pointwiseRead ->
        PkgSig bundle pointwiseRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row pointwiseRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨
                  hsame row R ∨ hsame row pointwiseRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont X F S ∧ Cont S Q R ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle pointwiseRead pkg)
              hsame ∧
            hsame pointwiseRead R ∧ UnaryHistory pointwiseRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier pointwiseRoute pointwisePkg
  obtain ⟨_xUnary, _fUnary, _sUnary, _qUnary, rUnary, _lUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, sourceApproxSchedule, scheduleReadbackReal, _realHandoffTransport,
    _transportContinuationProvenance, provenancePkg, _namePkg⟩ := carrier
  have pointwiseReal : hsame pointwiseRead R :=
    cont_deterministic pointwiseRoute scheduleReadbackReal
  have pointwiseUnary : UnaryHistory pointwiseRead :=
    unary_transport rUnary (hsame_symm pointwiseReal)
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row pointwiseRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨ hsame row R ∨
              hsame row pointwiseRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X F S ∧ Cont S Q R ∧
              PkgSig bundle P pkg ∧ PkgSig bundle pointwiseRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro pointwiseRead
        ⟨hsame_refl pointwiseRead, pointwiseUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceApproxSchedule, scheduleReadbackReal, provenancePkg,
          pointwisePkg⟩
  }
  exact ⟨cert, pointwiseReal, pointwiseUnary⟩

end BEDC.Derived.BaireOneFunctionUp
