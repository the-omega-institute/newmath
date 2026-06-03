import BEDC.Derived.RealUp.L10FaceLeantargetNoncollapse

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealL10FaceStatusProductReadback [AskSetup] [PackageSetup]
    {dyadic stream regseq sealRow transport route provenance localName sourceRoute streamRoute
      regseqRoute sealRoute interfaceRead terminalRead statusRead targetRead bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory dyadic →
      UnaryHistory stream →
        UnaryHistory regseq →
          UnaryHistory sealRow →
            UnaryHistory transport →
              UnaryHistory route →
                UnaryHistory provenance →
                  UnaryHistory localName →
                    Cont dyadic stream sourceRoute →
                      Cont sourceRoute regseq streamRoute →
                        Cont streamRoute sealRow regseqRoute →
                          Cont regseqRoute transport sealRoute →
                            Cont sealRoute localName interfaceRead →
                              Cont interfaceRead route terminalRead →
                                Cont terminalRead localName statusRead →
                                  Cont statusRead localName targetRead →
                                    Cont targetRead localName bridgeRead →
                                      PkgSig bundle provenance pkg →
                                        PkgSig bundle statusRead pkg →
                                          PkgSig bundle targetRead pkg →
                                            PkgSig bundle bridgeRead pkg →
                                              SemanticNameCert
                                                (fun row : BHist =>
                                                  hsame row statusRead ∨
                                                    hsame row targetRead ∨
                                                      hsame row bridgeRead)
                                                (fun row : BHist =>
                                                  hsame row dyadic ∨ hsame row stream ∨
                                                    hsame row regseq ∨ hsame row sealRow ∨
                                                      hsame row statusRead ∨
                                                        hsame row targetRead ∨
                                                          hsame row bridgeRead)
                                                (fun row : BHist =>
                                                  UnaryHistory row ∧
                                                    (PkgSig bundle statusRead pkg ∨
                                                      PkgSig bundle targetRead pkg ∨
                                                        PkgSig bundle bridgeRead pkg))
                                                hsame := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert
  intro dyadicUnary streamUnary regseqUnary sealUnary transportUnary routeUnary
    provenanceUnary localNameUnary dyadicStreamSource sourceRegseqStream streamSealRegseq
    regseqTransportSeal sealLocalNameInterface interfaceRouteTerminal terminalLocalNameStatus
    statusLocalNameTarget targetLocalNameBridge provenancePkg statusPkg targetPkg bridgePkg
  have readback :=
    RealL10FaceLeantargetNoncollapse (dyadic := dyadic) (stream := stream)
      (regseq := regseq) (sealRow := sealRow) (transport := transport) (route := route)
      (provenance := provenance) (localName := localName) (sourceRoute := sourceRoute)
      (streamRoute := streamRoute) (regseqRoute := regseqRoute) (sealRoute := sealRoute)
      (interfaceRead := interfaceRead) (terminalRead := terminalRead)
      (statusRead := statusRead) (targetRead := targetRead) (bridgeRead := bridgeRead)
      (bundle := bundle) (pkg := pkg)
      dyadicUnary streamUnary regseqUnary sealUnary transportUnary routeUnary provenanceUnary
      localNameUnary dyadicStreamSource sourceRegseqStream streamSealRegseq regseqTransportSeal
      sealLocalNameInterface interfaceRouteTerminal terminalLocalNameStatus statusLocalNameTarget
      targetLocalNameBridge provenancePkg statusPkg targetPkg bridgePkg
  obtain ⟨statusUnary, targetUnary, bridgeUnary, _terminalLocalNameStatus,
    _statusLocalNameTarget, _targetLocalNameBridge, _statusPkg, _targetPkg, _bridgePkg,
    _terminalE0Absurd, _terminalE1Absurd⟩ := readback
  exact {
    core := {
      carrier_inhabited := Exists.intro statusRead (Or.inl (hsame_refl statusRead))
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
        cases source with
        | inl rowStatus =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) rowStatus)
        | inr rest =>
            cases rest with
            | inl rowTarget =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowTarget))
            | inr rowBridge =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) rowBridge))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl rowStatus =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rowStatus))))
      | inr rest =>
          cases rest with
          | inl rowTarget =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rowTarget)))))
          | inr rowBridge =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rowBridge)))))
    ledger_sound := by
      intro row source
      cases source with
      | inl rowStatus =>
          exact
            ⟨unary_transport statusUnary (hsame_symm rowStatus), Or.inl statusPkg⟩
      | inr rest =>
          cases rest with
          | inl rowTarget =>
              exact
                ⟨unary_transport targetUnary (hsame_symm rowTarget),
                  Or.inr (Or.inl targetPkg)⟩
          | inr rowBridge =>
              exact
                ⟨unary_transport bridgeUnary (hsame_symm rowBridge),
                  Or.inr (Or.inr bridgePkg)⟩
  }

end BEDC.Derived.RealUp
