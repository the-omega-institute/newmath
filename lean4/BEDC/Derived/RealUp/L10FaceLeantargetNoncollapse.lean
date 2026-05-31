import BEDC.Derived.RealUp.L10FaceStatusNoncollapse

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealL10FaceLeantargetNoncollapse [AskSetup] [PackageSetup]
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
                                              UnaryHistory statusRead ∧
                                                UnaryHistory targetRead ∧
                                                  UnaryHistory bridgeRead ∧
                                                    Cont terminalRead localName statusRead ∧
                                                      Cont statusRead localName targetRead ∧
                                                        Cont targetRead localName bridgeRead ∧
                                                          PkgSig bundle statusRead pkg ∧
                                                            PkgSig bundle targetRead pkg ∧
                                                              PkgSig bundle bridgeRead pkg ∧
                                                                (Cont terminalRead
                                                                    (BHist.e0 dyadic)
                                                                    interfaceRead → False) ∧
                                                                  (Cont terminalRead
                                                                    (BHist.e1 sealRow)
                                                                    interfaceRead → False) := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro dyadicUnary streamUnary regseqUnary sealUnary transportUnary routeUnary
    provenanceUnary localNameUnary dyadicStreamSource sourceRegseqStream streamSealRegseq
    regseqTransportSeal sealLocalNameInterface interfaceRouteTerminal terminalLocalNameStatus
    statusLocalNameTarget targetLocalNameBridge provenancePkg statusPkg targetPkg bridgePkg
  have statusResult :=
    RealL10FaceStatusNoncollapse (dyadic := dyadic) (stream := stream)
      (regseq := regseq) (sealRow := sealRow) (transport := transport) (route := route)
      (provenance := provenance) (localName := localName) (sourceRoute := sourceRoute)
      (streamRoute := streamRoute) (regseqRoute := regseqRoute) (sealRoute := sealRoute)
      (interfaceRead := interfaceRead) (terminalRead := terminalRead)
      (statusRead := statusRead) (bundle := bundle) (pkg := pkg)
      dyadicUnary streamUnary regseqUnary sealUnary transportUnary routeUnary provenanceUnary
      localNameUnary dyadicStreamSource sourceRegseqStream streamSealRegseq regseqTransportSeal
      sealLocalNameInterface interfaceRouteTerminal terminalLocalNameStatus provenancePkg statusPkg
  obtain ⟨_terminalUnary, statusUnary, _dyadicStreamSource, _sourceRegseqStream,
    _streamSealRegseq, _regseqTransportSeal, _sealLocalNameInterface,
    _interfaceRouteTerminal, _terminalLocalNameStatus, _provenancePkg, _statusPkg,
    terminalE0Absurd, terminalE1Absurd⟩ := statusResult
  have targetUnary : UnaryHistory targetRead :=
    unary_cont_closed statusUnary localNameUnary statusLocalNameTarget
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed targetUnary localNameUnary targetLocalNameBridge
  exact
    ⟨statusUnary, targetUnary, bridgeUnary, terminalLocalNameStatus, statusLocalNameTarget,
      targetLocalNameBridge, statusPkg, targetPkg, bridgePkg, terminalE0Absurd,
      terminalE1Absurd⟩

end BEDC.Derived.RealUp
