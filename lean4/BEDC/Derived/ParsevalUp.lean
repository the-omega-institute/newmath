import BEDC.Derived.ParsevalUp.NameCertObligations
import BEDC.Derived.ParsevalUp.RootFourierIntegralEnergyExhaustion

namespace BEDC.Derived.ParsevalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ParsevalRootRealSealNonescape [AskSetup] [PackageSetup]
    {F S I E R D L H C P N coefficientRead integralRead dyadicRead sealRead namedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory F →
      UnaryHistory S →
        UnaryHistory I →
          UnaryHistory E →
            UnaryHistory R →
              UnaryHistory D →
                UnaryHistory L →
                  UnaryHistory H →
                    UnaryHistory C →
                      UnaryHistory N →
                        Cont F S coefficientRead →
                          Cont I E integralRead →
                            Cont coefficientRead R dyadicRead →
                              Cont dyadicRead L sealRead →
                                Cont sealRead N namedRead →
                                  PkgSig bundle P pkg →
                                    PkgSig bundle N pkg →
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row namedRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row F ∨ hsame row S ∨
                                              hsame row I ∨ hsame row E ∨
                                                hsame row R ∨ hsame row D ∨
                                                  hsame row L ∨ hsame row H ∨
                                                    hsame row C ∨ hsame row N ∨
                                                      hsame row namedRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧
                                              Cont F S coefficientRead ∧
                                                Cont I E integralRead ∧
                                                  Cont coefficientRead R dyadicRead ∧
                                                    Cont dyadicRead L sealRead ∧
                                                      Cont sealRead N namedRead ∧
                                                        PkgSig bundle P pkg ∧
                                                          PkgSig bundle N pkg)
                                          hsame ∧
                                        UnaryHistory coefficientRead ∧
                                          UnaryHistory integralRead ∧
                                            UnaryHistory dyadicRead ∧
                                              UnaryHistory sealRead ∧
                                                UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro fUnary sUnary iUnary eUnary rUnary _dUnary lUnary _hUnary _cUnary nUnary
    coefficientRoute integralRoute dyadicRoute sealRoute namedRoute provenancePkg namePkg
  have coefficientUnary : UnaryHistory coefficientRead :=
    unary_cont_closed fUnary sUnary coefficientRoute
  have integralUnary : UnaryHistory integralRead :=
    unary_cont_closed iUnary eUnary integralRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed coefficientUnary rUnary dyadicRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicUnary lUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row S ∨ hsame row I ∨ hsame row E ∨ hsame row R ∨
              hsame row D ∨ hsame row L ∨ hsame row H ∨ hsame row C ∨
                hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F S coefficientRead ∧ Cont I E integralRead ∧
              Cont coefficientRead R dyadicRead ∧ Cont dyadicRead L sealRead ∧
                Cont sealRead N namedRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, coefficientRoute, integralRoute, dyadicRoute, sealRoute,
          namedRoute, provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, coefficientUnary, integralUnary, dyadicUnary, sealUnary, namedUnary⟩

theorem ParsevalRealSealRefusalBoundary [AskSetup] [PackageSetup]
    {F S I E R D L H C P N coefficientRead integralRead dyadicRead sealRead namedRead
      refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory F →
      UnaryHistory S →
        UnaryHistory I →
          UnaryHistory E →
            UnaryHistory R →
              UnaryHistory D →
                UnaryHistory L →
                  UnaryHistory H →
                    UnaryHistory C →
                      UnaryHistory N →
                        Cont F S coefficientRead →
                          Cont I E integralRead →
                            Cont coefficientRead R dyadicRead →
                              Cont dyadicRead L sealRead →
                                Cont sealRead N namedRead →
                                  Cont L H refusalRead →
                                    PkgSig bundle P pkg →
                                      PkgSig bundle N pkg →
                                        PkgSig bundle refusalRead pkg →
                                          SemanticNameCert
                                              (fun row : BHist =>
                                                hsame row refusalRead ∧ UnaryHistory row)
                                              (fun row : BHist =>
                                                hsame row F ∨ hsame row S ∨
                                                  hsame row I ∨ hsame row E ∨
                                                    hsame row R ∨ hsame row D ∨
                                                      hsame row L ∨ hsame row H ∨
                                                        hsame row C ∨ hsame row N ∨
                                                          hsame row refusalRead)
                                              (fun row : BHist =>
                                                UnaryHistory row ∧
                                                  Cont F S coefficientRead ∧
                                                    Cont I E integralRead ∧
                                                      Cont coefficientRead R dyadicRead ∧
                                                        Cont dyadicRead L sealRead ∧
                                                          Cont sealRead N namedRead ∧
                                                            Cont L H refusalRead ∧
                                                              PkgSig bundle P pkg ∧
                                                                PkgSig bundle refusalRead pkg)
                                              hsame ∧
                                            UnaryHistory refusalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame SemanticNameCert
  intro fUnary sUnary iUnary eUnary rUnary _dUnary lUnary hUnary _cUnary _nUnary
    coefficientRoute integralRoute dyadicRoute sealRoute namedRoute refusalRoute provenancePkg
    _namePkg refusalPkg
  have coefficientUnary : UnaryHistory coefficientRead :=
    unary_cont_closed fUnary sUnary coefficientRoute
  have integralUnary : UnaryHistory integralRead :=
    unary_cont_closed iUnary eUnary integralRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed coefficientUnary rUnary dyadicRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicUnary lUnary sealRoute
  have _namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary _nUnary namedRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed lUnary hUnary refusalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row S ∨ hsame row I ∨ hsame row E ∨ hsame row R ∨
              hsame row D ∨ hsame row L ∨ hsame row H ∨ hsame row C ∨
                hsame row N ∨ hsame row refusalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F S coefficientRead ∧ Cont I E integralRead ∧
              Cont coefficientRead R dyadicRead ∧ Cont dyadicRead L sealRead ∧
                Cont sealRead N namedRead ∧ Cont L H refusalRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle refusalRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusalRead ⟨hsame_refl refusalRead, refusalUnary⟩
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
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, coefficientRoute, integralRoute, dyadicRoute, sealRoute, namedRoute,
          refusalRoute, provenancePkg, refusalPkg⟩
  }
  exact ⟨cert, refusalUnary⟩

theorem ParsevalRootRealEnergyNonescape [AskSetup] [PackageSetup]
    {fourier source pairing integral readback tolerance sealRow transport replay provenance name
      coefficientRead integralRead toleranceRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ParsevalCarrier fourier source pairing integral readback tolerance sealRow transport replay
        provenance name bundle pkg →
      Cont fourier source coefficientRead →
        Cont pairing integral integralRead →
          Cont integralRead tolerance toleranceRead →
            Cont toleranceRead sealRow sealRead →
              PkgSig bundle sealRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row fourier ∨ hsame row source ∨ hsame row pairing ∨
                        hsame row integral ∨ hsame row readback ∨ hsame row tolerance ∨
                          hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont fourier source coefficientRead ∧
                        Cont pairing integral integralRead ∧
                          Cont integralRead tolerance toleranceRead ∧
                            Cont toleranceRead sealRow sealRead ∧
                              PkgSig bundle sealRead pkg)
                    hsame ∧
                  UnaryHistory coefficientRead ∧ UnaryHistory integralRead ∧
                    UnaryHistory toleranceRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: ParsevalCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier coefficientRoute integralRoute toleranceRoute sealRoute sealPkg
  obtain ⟨fourierUnary, sourceUnary, pairingUnary, integralUnary, _readbackUnary,
    toleranceUnary, sealUnary, _transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    _fourierSourcePairing, _pairingIntegralReadback, _readbackToleranceSeal,
    _sealTransportReplay, _provenancePkg, _namePkg⟩ := carrier
  have coefficientUnary : UnaryHistory coefficientRead :=
    unary_cont_closed fourierUnary sourceUnary coefficientRoute
  have integralReadUnary : UnaryHistory integralRead :=
    unary_cont_closed pairingUnary integralUnary integralRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed integralReadUnary toleranceUnary toleranceRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceReadUnary sealUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row fourier ∨ hsame row source ∨ hsame row pairing ∨
              hsame row integral ∨ hsame row readback ∨ hsame row tolerance ∨
                hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont fourier source coefficientRead ∧
              Cont pairing integral integralRead ∧ Cont integralRead tolerance toleranceRead ∧
                Cont toleranceRead sealRow sealRead ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealReadUnary⟩
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
        ⟨source.right, coefficientRoute, integralRoute, toleranceRoute, sealRoute, sealPkg⟩
  }
  exact ⟨cert, coefficientUnary, integralReadUnary, toleranceReadUnary, sealReadUnary⟩

theorem ParsevalRootObligationSurface [AskSetup] [PackageSetup]
    {fourier source pairing integral readback tolerance sealRow transport replay provenance name
      coefficientRead energyRead toleranceRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ParsevalCarrier fourier source pairing integral readback tolerance sealRow transport replay
        provenance name bundle pkg →
      Cont fourier source coefficientRead →
        Cont pairing integral energyRead →
          Cont energyRead tolerance toleranceRead →
            Cont toleranceRead sealRow sealRead →
              Cont sealRead name namedRead →
                PkgSig bundle namedRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row fourier ∨ hsame row source ∨ hsame row pairing ∨
                          hsame row integral ∨ hsame row tolerance ∨ hsame row sealRow ∨
                            hsame row coefficientRead ∨ hsame row energyRead ∨
                              hsame row toleranceRead ∨ hsame row namedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont fourier source coefficientRead ∧
                          Cont pairing integral energyRead ∧
                            Cont energyRead tolerance toleranceRead ∧
                              Cont toleranceRead sealRow sealRead ∧
                                Cont sealRead name namedRead ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle namedRead pkg)
                      hsame ∧
                    UnaryHistory coefficientRead ∧ UnaryHistory energyRead ∧
                      UnaryHistory toleranceRead ∧ UnaryHistory sealRead ∧
                        UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: ParsevalCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier coefficientRoute energyRoute toleranceRoute sealRoute namedRoute namedPkg
  obtain ⟨fourierUnary, sourceUnary, pairingUnary, integralUnary, _readbackUnary,
    toleranceUnary, sealUnary, _transportUnary, _replayUnary, _provenanceUnary, nameUnary,
    _fourierSourcePairing, _pairingIntegralReadback, _readbackToleranceSeal,
    _sealTransportReplay, provenancePkg, _namePkg⟩ := carrier
  have coefficientUnary : UnaryHistory coefficientRead :=
    unary_cont_closed fourierUnary sourceUnary coefficientRoute
  have energyUnary : UnaryHistory energyRead :=
    unary_cont_closed pairingUnary integralUnary energyRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed energyUnary toleranceUnary toleranceRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceReadUnary sealUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealReadUnary nameUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row fourier ∨ hsame row source ∨ hsame row pairing ∨
              hsame row integral ∨ hsame row tolerance ∨ hsame row sealRow ∨
                hsame row coefficientRead ∨ hsame row energyRead ∨
                  hsame row toleranceRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont fourier source coefficientRead ∧
              Cont pairing integral energyRead ∧ Cont energyRead tolerance toleranceRead ∧
                Cont toleranceRead sealRow sealRead ∧ Cont sealRead name namedRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, coefficientRoute, energyRoute, toleranceRoute, sealRoute,
          namedRoute, provenancePkg, namedPkg⟩
  }
  exact
    ⟨cert, coefficientUnary, energyUnary, toleranceReadUnary, sealReadUnary, namedUnary⟩

end BEDC.Derived.ParsevalUp
