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

end BEDC.Derived.BaireOneFunctionUp
