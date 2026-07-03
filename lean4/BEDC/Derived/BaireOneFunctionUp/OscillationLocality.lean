import BEDC.Derived.BaireOneFunctionUp

namespace BEDC.Derived.BaireOneFunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireOneFunctionCarrier_oscillation_locality [AskSetup] [PackageSetup]
    {X F S Q R L H C P N oscillationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg ->
      Cont X F S ->
        Cont S Q R ->
          Cont R L oscillationRead ->
            PkgSig bundle oscillationRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row oscillationRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨
                      hsame row R ∨ hsame row L ∨ hsame row oscillationRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont X F S ∧ Cont S Q R ∧
                      Cont R L oscillationRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle oscillationRead pkg)
                  hsame ∧
                UnaryHistory oscillationRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier sourceApproxSchedule scheduleReadbackReal realOscillationRead
    oscillationPkg
  obtain ⟨_xUnary, _fUnary, _sUnary, _qUnary, realUnary, handoffUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _carrierSourceApproxSchedule,
    _carrierScheduleReadbackReal, _carrierRealHandoffTransport,
    _transportContinuationProvenance, provenancePkg, _namePkg⟩ := carrier
  have oscillationUnary : UnaryHistory oscillationRead :=
    unary_cont_closed realUnary handoffUnary realOscillationRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row oscillationRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨ hsame row R ∨
              hsame row L ∨ hsame row oscillationRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X F S ∧ Cont S Q R ∧ Cont R L oscillationRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle oscillationRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro oscillationRead
        ⟨hsame_refl oscillationRead, oscillationUnary⟩
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
      exact
        ⟨source.right, sourceApproxSchedule, scheduleReadbackReal, realOscillationRead,
          provenancePkg, oscillationPkg⟩
  }
  exact ⟨cert, oscillationUnary⟩

theorem BaireOneFunctionCarrier_public_export_locality_boundary [AskSetup] [PackageSetup]
    {X F S Q R L H C P N publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg →
      Cont L C publicRead →
        PkgSig bundle publicRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨
                  hsame row R ∨ hsame row L ∨ hsame row H ∨ hsame row C ∨
                    hsame row P ∨ hsame row N ∨ hsame row publicRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont X F S ∧ Cont S Q R ∧ Cont R L H ∧
                  Cont L C publicRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                    PkgSig bundle publicRead pkg)
              hsame ∧
            UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier publicRoute publicPkg
  have exported :=
    BaireOneFunctionCarrier_public_export
      (X := X) (F := F) (S := S) (Q := Q) (R := R) (L := L) (H := H)
      (C := C) (P := P) (N := N) (publicRead := publicRead) (bundle := bundle)
      (pkg := pkg) carrier publicRoute publicPkg
  obtain ⟨_xUnary, _fUnary, _sUnary, _qUnary, _rUnary, _lUnary, _hUnary, _cUnary,
    publicUnary, sourceApproxSchedule, scheduleReadbackReal, realHandoffTransport,
    exportedPublicRoute, provenancePkg, namePkg, exportedPublicPkg⟩ := exported
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨ hsame row R ∨
              hsame row L ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X F S ∧ Cont S Q R ∧ Cont R L H ∧
              Cont L C publicRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      intro _row source
      exact
        ⟨source.right, sourceApproxSchedule, scheduleReadbackReal, realHandoffTransport,
          exportedPublicRoute, provenancePkg, namePkg, exportedPublicPkg⟩
  }
  exact ⟨cert, publicUnary⟩

theorem BaireOneFunctionCarrier_lowersemicontinuous_public_route [AskSetup] [PackageSetup]
    {X F S Q R L H C P N lscRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg →
      Cont R L lscRead →
        PkgSig bundle lscRead pkg →
          Cont L C publicRead →
            PkgSig bundle publicRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row lscRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨
                      hsame row R ∨ hsame row L ∨ hsame row lscRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont R L lscRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle lscRead pkg)
                  hsame ∧
                SemanticNameCert
                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨
                        hsame row R ∨ hsame row L ∨ hsame row H ∨ hsame row C ∨
                          hsame row P ∨ hsame row N ∨ hsame row publicRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont X F S ∧ Cont S Q R ∧ Cont R L H ∧
                        Cont L C publicRead ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle N pkg ∧ PkgSig bundle publicRead pkg)
                    hsame ∧
                  UnaryHistory lscRead ∧ UnaryHistory publicRead ∧ Cont X F S ∧
                    Cont S Q R ∧ Cont L C publicRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier lscRoute lscPkg publicRoute publicPkg
  have lscHandoff :=
    BaireOneFunctionCarrier_lowersemicontinuous_handoff
      (X := X) (F := F) (S := S) (Q := Q) (R := R) (L := L) (H := H)
      (C := C) (P := P) (N := N) (lscRead := lscRead) (bundle := bundle)
      (pkg := pkg) carrier lscRoute lscPkg
  obtain ⟨lscCert, lscUnary, sourceApproxSchedule, scheduleReadbackReal,
    provenancePkg⟩ := lscHandoff
  have publicBoundary :=
    BaireOneFunctionCarrier_public_export_locality_boundary
      (X := X) (F := F) (S := S) (Q := Q) (R := R) (L := L) (H := H)
      (C := C) (P := P) (N := N) (publicRead := publicRead) (bundle := bundle)
      (pkg := pkg) carrier publicRoute publicPkg
  obtain ⟨publicCert, publicUnary⟩ := publicBoundary
  exact
    ⟨lscCert, publicCert, lscUnary, publicUnary, sourceApproxSchedule,
      scheduleReadbackReal, publicRoute, provenancePkg, publicPkg⟩

theorem BaireOneFunctionCarrier_oscillation_schedule_boundary [AskSetup] [PackageSetup]
    {X F S Q R L H C P N oscillationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg →
      Cont R L oscillationRead →
        PkgSig bundle oscillationRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row H ∧ BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg)
              (fun row : BHist =>
                hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨
                  hsame row R ∨ hsame row L ∨ hsame row H ∨ hsame row C ∨
                    hsame row P ∨ hsame row N)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
              hsame ∧
            SemanticNameCert
                (fun row : BHist => hsame row oscillationRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨
                    hsame row R ∨ hsame row L ∨ hsame row oscillationRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont X F S ∧ Cont S Q R ∧
                    Cont R L oscillationRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle oscillationRead pkg)
                hsame ∧
              UnaryHistory oscillationRead ∧ Cont X F S ∧ Cont S Q R ∧
                Cont R L H := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier realOscillationRead oscillationPkg
  have scheduled :=
    _root_.BEDC.Derived.BaireOneFunctionUp.BaireOneFunctionCarrier_pointwise_schedule_obligations
      (X := X) (F := F) (S := S) (Q := Q) (R := R) (L := L) (H := H)
      (C := C) (P := P) (N := N) (bundle := bundle) (pkg := pkg) carrier
  obtain ⟨scheduleCert, _xUnary, _fUnary, _sUnary, _qUnary, _rUnary, _lUnary,
    _hUnary, _cUnary, _provenancePkg, _namePkg, sourceApproxSchedule,
    scheduleReadbackReal, realHandoffTransport⟩ := scheduled
  have locality :=
    BaireOneFunctionCarrier_oscillation_locality
      (X := X) (F := F) (S := S) (Q := Q) (R := R) (L := L) (H := H)
      (C := C) (P := P) (N := N) (oscillationRead := oscillationRead)
      (bundle := bundle) (pkg := pkg) carrier sourceApproxSchedule scheduleReadbackReal
      realOscillationRead oscillationPkg
  obtain ⟨localityCert, oscillationUnary⟩ := locality
  exact
    ⟨scheduleCert, localityCert, oscillationUnary, sourceApproxSchedule,
      scheduleReadbackReal, realHandoffTransport⟩

theorem BaireOneFunctionCarrier_pointwise_oscillation_handoff [AskSetup] [PackageSetup]
    {X F S Q R L H C P N pointwiseRead oscillationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg →
      Cont S Q pointwiseRead →
        PkgSig bundle pointwiseRead pkg →
          Cont R L oscillationRead →
            PkgSig bundle oscillationRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row pointwiseRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨
                      hsame row pointwiseRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle pointwiseRead pkg ∧ Cont S Q pointwiseRead)
                  hsame ∧
                SemanticNameCert
                    (fun row : BHist => hsame row oscillationRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨
                        hsame row R ∨ hsame row L ∨ hsame row oscillationRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont X F S ∧ Cont S Q R ∧
                        Cont R L oscillationRead ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle oscillationRead pkg)
                    hsame ∧
                  UnaryHistory pointwiseRead ∧ UnaryHistory oscillationRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier pointwiseRoute pointwisePkg oscillationRoute oscillationPkg
  have carrierWhole := carrier
  obtain ⟨_xUnary, _fUnary, scheduleUnary, readbackUnary, _rUnary, _lUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, sourceApproxSchedule,
    scheduleReadbackReal, _realHandoffTransport, _transportContinuationProvenance,
    provenancePkg, _namePkg⟩ := carrier
  have pointwiseUnary : UnaryHistory pointwiseRead :=
    unary_cont_closed scheduleUnary readbackUnary pointwiseRoute
  have pointwiseCert :
      SemanticNameCert
          (fun row : BHist => hsame row pointwiseRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨
              hsame row pointwiseRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle pointwiseRead pkg ∧
              Cont S Q pointwiseRead)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, pointwisePkg, pointwiseRoute⟩
  }
  have locality :=
    BaireOneFunctionCarrier_oscillation_locality
      (X := X) (F := F) (S := S) (Q := Q) (R := R) (L := L) (H := H)
      (C := C) (P := P) (N := N) (oscillationRead := oscillationRead)
      (bundle := bundle) (pkg := pkg) carrierWhole sourceApproxSchedule scheduleReadbackReal
      oscillationRoute oscillationPkg
  obtain ⟨oscillationCert, oscillationUnary⟩ := locality
  exact ⟨pointwiseCert, oscillationCert, pointwiseUnary, oscillationUnary⟩

theorem BaireOneFunctionCarrier_pointwise_lowersemicontinuous_handoff_certificate
    [AskSetup] [PackageSetup]
    {X F S Q R L H C P N pointwiseRead lscRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg ->
      Cont S Q pointwiseRead ->
        PkgSig bundle pointwiseRead pkg ->
          Cont R L lscRead ->
            PkgSig bundle lscRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row pointwiseRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨
                      hsame row pointwiseRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle pointwiseRead pkg ∧ Cont S Q pointwiseRead)
                  hsame ∧
                SemanticNameCert
                    (fun row : BHist => hsame row lscRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨
                        hsame row R ∨ hsame row L ∨ hsame row lscRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont R L lscRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle lscRead pkg)
                    hsame ∧
                  UnaryHistory pointwiseRead ∧ UnaryHistory lscRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier pointwiseRoute pointwisePkg lscRoute lscPkg
  have carrierWhole := carrier
  obtain ⟨_xUnary, _fUnary, scheduleUnary, readbackUnary, _realUnary, _handoffUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _sourceApproxSchedule, _scheduleReadbackReal,
    _realHandoffTransport, _transportContinuationProvenance, provenancePkg, _namePkg⟩ :=
    carrier
  have pointwiseUnary : UnaryHistory pointwiseRead :=
    unary_cont_closed scheduleUnary readbackUnary pointwiseRoute
  have pointwiseCert :
      SemanticNameCert
          (fun row : BHist => hsame row pointwiseRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨
              hsame row pointwiseRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle pointwiseRead pkg ∧
              Cont S Q pointwiseRead)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, pointwisePkg, pointwiseRoute⟩
  }
  have lscHandoff :=
    BaireOneFunctionCarrier_lowersemicontinuous_handoff
      (X := X) (F := F) (S := S) (Q := Q) (R := R) (L := L) (H := H)
      (C := C) (P := P) (N := N) (lscRead := lscRead) (bundle := bundle)
      (pkg := pkg) carrierWhole lscRoute lscPkg
  obtain ⟨lscCert, lscUnary, _sourceApproxSchedule, _scheduleReadbackReal,
    _provenancePkg⟩ := lscHandoff
  exact ⟨pointwiseCert, lscCert, pointwiseUnary, lscUnary⟩

theorem BaireOneFunctionCarrier_lowersemicontinuous_exhaustion [AskSetup] [PackageSetup]
    {X F S Q R L H C P N lscRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg ->
      Cont R L lscRead ->
        PkgSig bundle lscRead pkg ->
          Cont L C publicRead ->
            PkgSig bundle publicRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row lscRead ∨ hsame row publicRead) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨
                      hsame row R ∨ hsame row L ∨ hsame row H ∨ hsame row C ∨
                        hsame row P ∨ hsame row N ∨ hsame row lscRead ∨
                          hsame row publicRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont R L lscRead ∧ Cont L C publicRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg)
                  hsame ∧
                UnaryHistory lscRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier lscRoute lscPkg publicRoute publicPkg
  have lscHandoff :=
    BaireOneFunctionCarrier_lowersemicontinuous_handoff
      (X := X) (F := F) (S := S) (Q := Q) (R := R) (L := L) (H := H)
      (C := C) (P := P) (N := N) (lscRead := lscRead) (bundle := bundle)
      (pkg := pkg) carrier lscRoute lscPkg
  obtain ⟨_lscCert, lscUnary, _sourceApproxSchedule, _scheduleReadbackReal,
    provenancePkg⟩ := lscHandoff
  have publicBoundary :=
    BaireOneFunctionCarrier_public_export_locality_boundary
      (X := X) (F := F) (S := S) (Q := Q) (R := R) (L := L) (H := H)
      (C := C) (P := P) (N := N) (publicRead := publicRead) (bundle := bundle)
      (pkg := pkg) carrier publicRoute publicPkg
  obtain ⟨_publicCert, publicUnary⟩ := publicBoundary
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row lscRead ∨ hsame row publicRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨ hsame row R ∨
              hsame row L ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row lscRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R L lscRead ∧ Cont L C publicRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro lscRead
        ⟨Or.inl (hsame_refl lscRead), lscUnary⟩
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
          | inl sameLsc =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameLsc)
          | inr samePublic =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) samePublic)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameLsc =>
          exact
            Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
              Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl sameLsc
      | inr samePublic =>
          exact
            Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
              Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr samePublic
    ledger_sound := by
      intro _row source
      exact ⟨source.right, lscRoute, publicRoute, provenancePkg, publicPkg⟩
  }
  exact ⟨cert, lscUnary, publicUnary⟩

theorem BaireOneFunctionCarrier_finite_schedule_oscillation_boundary
    [AskSetup] [PackageSetup]
    {X F S Q R L H C P N pointwiseRead lscRead publicRead oscillationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg ->
      Cont S Q pointwiseRead ->
        Cont R L lscRead ->
          Cont L C publicRead ->
            PkgSig bundle publicRead pkg ->
              Cont R L oscillationRead ->
                PkgSig bundle oscillationRead pkg ->
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row pointwiseRead ∨ hsame row lscRead ∨
                            hsame row publicRead) ∧
                          UnaryHistory row)
                      (fun row : BHist =>
                        hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨
                          hsame row R ∨ hsame row L ∨ hsame row H ∨ hsame row C ∨
                            hsame row P ∨ hsame row N ∨ hsame row pointwiseRead ∨
                              hsame row lscRead ∨ hsame row publicRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont S Q pointwiseRead ∧ Cont R L lscRead ∧
                          Cont L C publicRead ∧ PkgSig bundle publicRead pkg)
                      hsame ∧
                    SemanticNameCert
                        (fun row : BHist =>
                          hsame row H ∧
                            BaireOneFunctionCarrier X F S Q R L H C P N bundle pkg)
                        (fun row : BHist =>
                          hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨
                            hsame row R ∨ hsame row L ∨ hsame row H ∨ hsame row C ∨
                              hsame row P ∨ hsame row N)
                        (fun row : BHist =>
                          UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                        hsame ∧
                      SemanticNameCert
                          (fun row : BHist => hsame row oscillationRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row X ∨ hsame row F ∨ hsame row S ∨ hsame row Q ∨
                              hsame row R ∨ hsame row L ∨ hsame row oscillationRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont X F S ∧ Cont S Q R ∧
                              Cont R L oscillationRead ∧ PkgSig bundle P pkg ∧
                                PkgSig bundle oscillationRead pkg)
                          hsame ∧
                        UnaryHistory pointwiseRead ∧ UnaryHistory lscRead ∧
                          UnaryHistory publicRead ∧ UnaryHistory oscillationRead ∧
                            Cont X F S ∧ Cont S Q R ∧ Cont R L H := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier pointwiseRoute lscRoute publicRoute publicPkg oscillationRoute
    oscillationPkg
  have finiteSchedule :=
    _root_.BEDC.Derived.BaireOneFunctionUp.BaireOneFunctionCarrier_finite_schedule_nonescape
      (X := X) (F := F) (S := S) (Q := Q) (R := R) (L := L) (H := H)
      (C := C) (P := P) (N := N) (pointwiseRead := pointwiseRead)
      (lscRead := lscRead) (publicRead := publicRead) (bundle := bundle)
      (pkg := pkg) carrier pointwiseRoute lscRoute publicRoute publicPkg
  obtain ⟨finiteCert, pointwiseUnary, lscUnary, publicUnary⟩ := finiteSchedule
  have oscillationBoundary :=
    BaireOneFunctionCarrier_oscillation_schedule_boundary
      (X := X) (F := F) (S := S) (Q := Q) (R := R) (L := L) (H := H)
      (C := C) (P := P) (N := N) (oscillationRead := oscillationRead)
      (bundle := bundle) (pkg := pkg) carrier oscillationRoute oscillationPkg
  obtain ⟨scheduleCert, oscillationCert, oscillationUnary, sourceApproxSchedule,
    scheduleReadbackReal, realHandoffTransport⟩ := oscillationBoundary
  exact
    ⟨finiteCert, scheduleCert, oscillationCert, pointwiseUnary, lscUnary, publicUnary,
      oscillationUnary, sourceApproxSchedule, scheduleReadbackReal, realHandoffTransport⟩

end BEDC.Derived.BaireOneFunctionUp
