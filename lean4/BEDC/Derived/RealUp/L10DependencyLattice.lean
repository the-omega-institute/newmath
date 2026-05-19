import BEDC.Derived.RealUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealL10DependencyLattice_source_route_nonescape [AskSetup] [PackageSetup]
    {dyadic stream regseq sealRow transport route provenance localName sourceRoute streamRoute
      regseqRoute sealRoute : BHist}
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
                            PkgSig bundle provenance pkg →
                              PkgSig bundle sealRoute pkg →
                                UnaryHistory sourceRoute ∧ UnaryHistory streamRoute ∧
                                  UnaryHistory regseqRoute ∧ UnaryHistory sealRoute ∧
                                    Cont dyadic stream sourceRoute ∧
                                      Cont sourceRoute regseq streamRoute ∧
                                        Cont streamRoute sealRow regseqRoute ∧
                                          Cont regseqRoute transport sealRoute ∧
                                            PkgSig bundle provenance pkg ∧
                                              PkgSig bundle sealRoute pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro dyadicUnary streamUnary regseqUnary sealUnary transportUnary _routeUnary
    _provenanceUnary _localNameUnary dyadicStreamSource sourceRegseqStream
    streamSealRegseq regseqTransportSeal provenancePkg sealPkg
  have sourceUnary : UnaryHistory sourceRoute :=
    unary_cont_closed dyadicUnary streamUnary dyadicStreamSource
  have streamRouteUnary : UnaryHistory streamRoute :=
    unary_cont_closed sourceUnary regseqUnary sourceRegseqStream
  have regseqRouteUnary : UnaryHistory regseqRoute :=
    unary_cont_closed streamRouteUnary sealUnary streamSealRegseq
  have sealRouteUnary : UnaryHistory sealRoute :=
    unary_cont_closed regseqRouteUnary transportUnary regseqTransportSeal
  exact
    ⟨sourceUnary, streamRouteUnary, regseqRouteUnary, sealRouteUnary, dyadicStreamSource,
      sourceRegseqStream, streamSealRegseq, regseqTransportSeal, provenancePkg, sealPkg⟩

theorem RealL10DependencyLatticeInterfaceTotality [AskSetup] [PackageSetup]
    {dyadic stream regseq sealRow transport route provenance localName sourceRoute streamRoute
      regseqRoute sealRoute interfaceRead : BHist}
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
                              PkgSig bundle provenance pkg →
                                PkgSig bundle interfaceRead pkg →
                                  UnaryHistory sourceRoute ∧ UnaryHistory streamRoute ∧
                                    UnaryHistory regseqRoute ∧ UnaryHistory sealRoute ∧
                                      UnaryHistory interfaceRead ∧
                                        Cont dyadic stream sourceRoute ∧
                                          Cont sourceRoute regseq streamRoute ∧
                                            Cont streamRoute sealRow regseqRoute ∧
                                              Cont regseqRoute transport sealRoute ∧
                                                Cont sealRoute localName interfaceRead ∧
                                                  PkgSig bundle provenance pkg ∧
                                                    PkgSig bundle interfaceRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro dyadicUnary streamUnary regseqUnary sealUnary transportUnary _routeUnary
    _provenanceUnary localNameUnary dyadicStreamSource sourceRegseqStream
    streamSealRegseq regseqTransportSeal sealLocalNameInterface provenancePkg interfacePkg
  have sourceUnary : UnaryHistory sourceRoute :=
    unary_cont_closed dyadicUnary streamUnary dyadicStreamSource
  have streamRouteUnary : UnaryHistory streamRoute :=
    unary_cont_closed sourceUnary regseqUnary sourceRegseqStream
  have regseqRouteUnary : UnaryHistory regseqRoute :=
    unary_cont_closed streamRouteUnary sealUnary streamSealRegseq
  have sealRouteUnary : UnaryHistory sealRoute :=
    unary_cont_closed regseqRouteUnary transportUnary regseqTransportSeal
  have interfaceUnary : UnaryHistory interfaceRead :=
    unary_cont_closed sealRouteUnary localNameUnary sealLocalNameInterface
  exact
    ⟨sourceUnary, streamRouteUnary, regseqRouteUnary, sealRouteUnary, interfaceUnary,
      dyadicStreamSource, sourceRegseqStream, streamSealRegseq, regseqTransportSeal,
      sealLocalNameInterface, provenancePkg, interfacePkg⟩

theorem RealL10TerminalFourFaceCorrespondence [AskSetup] [PackageSetup]
    {dyadic stream regseq sealRow transport route provenance localName sourceRoute streamRoute
      regseqRoute sealRoute interfaceRead terminalRead : BHist}
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
                                PkgSig bundle provenance pkg →
                                  PkgSig bundle terminalRead pkg →
                                    UnaryHistory terminalRead ∧
                                      Cont dyadic stream sourceRoute ∧
                                        Cont sourceRoute regseq streamRoute ∧
                                          Cont streamRoute sealRow regseqRoute ∧
                                            Cont regseqRoute transport sealRoute ∧
                                              Cont sealRoute localName interfaceRead ∧
                                                Cont interfaceRead route terminalRead ∧
                                                  PkgSig bundle provenance pkg ∧
                                                    PkgSig bundle terminalRead pkg ∧
                                                      (Cont terminalRead (BHist.e0 dyadic)
                                                          interfaceRead -> False) ∧
                                                        (Cont terminalRead (BHist.e1 sealRow)
                                                          interfaceRead -> False) := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro dyadicUnary streamUnary regseqUnary sealUnary transportUnary routeUnary
    _provenanceUnary localNameUnary dyadicStreamSource sourceRegseqStream
    streamSealRegseq regseqTransportSeal sealLocalNameInterface interfaceRouteTerminal
    provenancePkg terminalPkg
  have sourceUnary : UnaryHistory sourceRoute :=
    unary_cont_closed dyadicUnary streamUnary dyadicStreamSource
  have streamRouteUnary : UnaryHistory streamRoute :=
    unary_cont_closed sourceUnary regseqUnary sourceRegseqStream
  have regseqRouteUnary : UnaryHistory regseqRoute :=
    unary_cont_closed streamRouteUnary sealUnary streamSealRegseq
  have sealRouteUnary : UnaryHistory sealRoute :=
    unary_cont_closed regseqRouteUnary transportUnary regseqTransportSeal
  have interfaceUnary : UnaryHistory interfaceRead :=
    unary_cont_closed sealRouteUnary localNameUnary sealLocalNameInterface
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed interfaceUnary routeUnary interfaceRouteTerminal
  exact
    ⟨terminalUnary, dyadicStreamSource, sourceRegseqStream, streamSealRegseq,
      regseqTransportSeal, sealLocalNameInterface, interfaceRouteTerminal, provenancePkg,
      terminalPkg, (cont_mutual_extension_right_tail_absurd.left interfaceRouteTerminal),
      (cont_mutual_extension_right_tail_absurd.right interfaceRouteTerminal)⟩

theorem RealL10TerminalPullbackUniqueness [AskSetup] [PackageSetup]
    {dyadic stream regseq sealRow transport route provenance localName sourceRoute streamRoute
      regseqRoute sealRoute interfaceRead terminalA terminalB : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory dyadic ->
      UnaryHistory stream ->
        UnaryHistory regseq ->
          UnaryHistory sealRow ->
            UnaryHistory transport ->
              UnaryHistory route ->
                UnaryHistory provenance ->
                  UnaryHistory localName ->
                    Cont dyadic stream sourceRoute ->
                      Cont sourceRoute regseq streamRoute ->
                        Cont streamRoute sealRow regseqRoute ->
                          Cont regseqRoute transport sealRoute ->
                            Cont sealRoute localName interfaceRead ->
                              Cont interfaceRead route terminalA ->
                                Cont interfaceRead route terminalB ->
                                  PkgSig bundle provenance pkg ->
                                    PkgSig bundle terminalA pkg ->
                                      PkgSig bundle terminalB pkg ->
                                        hsame terminalA terminalB ∧ UnaryHistory terminalA ∧
                                          UnaryHistory terminalB ∧
                                            PkgSig bundle provenance pkg ∧
                                              PkgSig bundle terminalA pkg ∧
                                                PkgSig bundle terminalB pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig hsame
  intro dyadicUnary streamUnary regseqUnary sealUnary transportUnary routeUnary
    _provenanceUnary localNameUnary dyadicStreamSource sourceRegseqStream
    streamSealRegseq regseqTransportSeal sealLocalNameInterface interfaceRouteTerminalA
    interfaceRouteTerminalB provenancePkg terminalAPkg terminalBPkg
  have sourceUnary : UnaryHistory sourceRoute :=
    unary_cont_closed dyadicUnary streamUnary dyadicStreamSource
  have streamRouteUnary : UnaryHistory streamRoute :=
    unary_cont_closed sourceUnary regseqUnary sourceRegseqStream
  have regseqRouteUnary : UnaryHistory regseqRoute :=
    unary_cont_closed streamRouteUnary sealUnary streamSealRegseq
  have sealRouteUnary : UnaryHistory sealRoute :=
    unary_cont_closed regseqRouteUnary transportUnary regseqTransportSeal
  have interfaceUnary : UnaryHistory interfaceRead :=
    unary_cont_closed sealRouteUnary localNameUnary sealLocalNameInterface
  have terminalAUnary : UnaryHistory terminalA :=
    unary_cont_closed interfaceUnary routeUnary interfaceRouteTerminalA
  have terminalBUnary : UnaryHistory terminalB :=
    unary_cont_closed interfaceUnary routeUnary interfaceRouteTerminalB
  have sameTerminal : hsame terminalA terminalB :=
    cont_respects_hsame (hsame_refl interfaceRead) (hsame_refl route)
      interfaceRouteTerminalA interfaceRouteTerminalB
  exact
    ⟨sameTerminal, terminalAUnary, terminalBUnary, provenancePkg, terminalAPkg,
      terminalBPkg⟩

theorem RealL10TerminalSourceLock [AskSetup] [PackageSetup]
    {dyadic stream regseq sealRow transport route provenance localName sourceRoute streamRoute
      regseqRoute sealRoute interfaceRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory dyadic ->
      UnaryHistory stream ->
        UnaryHistory regseq ->
          UnaryHistory sealRow ->
            UnaryHistory transport ->
              UnaryHistory route ->
                UnaryHistory provenance ->
                  UnaryHistory localName ->
                    Cont dyadic stream sourceRoute ->
                      Cont sourceRoute regseq streamRoute ->
                        Cont streamRoute sealRow regseqRoute ->
                          Cont regseqRoute transport sealRoute ->
                            Cont sealRoute localName interfaceRead ->
                              Cont interfaceRead route terminalRead ->
                                PkgSig bundle provenance pkg ->
                                  PkgSig bundle terminalRead pkg ->
                                    UnaryHistory sourceRoute ∧ UnaryHistory streamRoute ∧
                                      UnaryHistory regseqRoute ∧ UnaryHistory sealRoute ∧
                                        UnaryHistory interfaceRead ∧ UnaryHistory terminalRead ∧
                                          Cont dyadic stream sourceRoute ∧
                                            Cont sourceRoute regseq streamRoute ∧
                                              Cont streamRoute sealRow regseqRoute ∧
                                                Cont regseqRoute transport sealRoute ∧
                                                  Cont sealRoute localName interfaceRead ∧
                                                    Cont interfaceRead route terminalRead ∧
                                                      PkgSig bundle provenance pkg ∧
                                                        PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro dyadicUnary streamUnary regseqUnary sealUnary transportUnary routeUnary
    _provenanceUnary localNameUnary dyadicStreamSource sourceRegseqStream
    streamSealRegseq regseqTransportSeal sealLocalNameInterface interfaceRouteTerminal
    provenancePkg terminalPkg
  have sourceUnary : UnaryHistory sourceRoute :=
    unary_cont_closed dyadicUnary streamUnary dyadicStreamSource
  have streamRouteUnary : UnaryHistory streamRoute :=
    unary_cont_closed sourceUnary regseqUnary sourceRegseqStream
  have regseqRouteUnary : UnaryHistory regseqRoute :=
    unary_cont_closed streamRouteUnary sealUnary streamSealRegseq
  have sealRouteUnary : UnaryHistory sealRoute :=
    unary_cont_closed regseqRouteUnary transportUnary regseqTransportSeal
  have interfaceUnary : UnaryHistory interfaceRead :=
    unary_cont_closed sealRouteUnary localNameUnary sealLocalNameInterface
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed interfaceUnary routeUnary interfaceRouteTerminal
  exact
    ⟨sourceUnary, streamRouteUnary, regseqRouteUnary, sealRouteUnary, interfaceUnary,
      terminalUnary, dyadicStreamSource, sourceRegseqStream, streamSealRegseq,
      regseqTransportSeal, sealLocalNameInterface, interfaceRouteTerminal, provenancePkg,
      terminalPkg⟩

end BEDC.Derived.RealUp
