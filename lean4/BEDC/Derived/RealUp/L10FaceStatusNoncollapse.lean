import BEDC.Derived.RealUp.L10DependencyLattice

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealL10FaceStatusNoncollapse [AskSetup] [PackageSetup]
    {dyadic stream regseq sealRow transport route provenance localName sourceRoute streamRoute
      regseqRoute sealRoute interfaceRead terminalRead statusRead : BHist}
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
                                  PkgSig bundle provenance pkg →
                                    PkgSig bundle statusRead pkg →
                                      UnaryHistory terminalRead ∧ UnaryHistory statusRead ∧
                                        Cont dyadic stream sourceRoute ∧
                                          Cont sourceRoute regseq streamRoute ∧
                                            Cont streamRoute sealRow regseqRoute ∧
                                              Cont regseqRoute transport sealRoute ∧
                                                Cont sealRoute localName interfaceRead ∧
                                                  Cont interfaceRead route terminalRead ∧
                                                    Cont terminalRead localName statusRead ∧
                                                      PkgSig bundle provenance pkg ∧
                                                        PkgSig bundle statusRead pkg ∧
                                                          (Cont terminalRead (BHist.e0 dyadic)
                                                              interfaceRead → False) ∧
                                                            (Cont terminalRead (BHist.e1 sealRow)
                                                              interfaceRead → False) := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro dyadicUnary streamUnary regseqUnary sealUnary transportUnary routeUnary
    _provenanceUnary localNameUnary dyadicStreamSource sourceRegseqStream
    streamSealRegseq regseqTransportSeal sealLocalNameInterface interfaceRouteTerminal
    terminalLocalNameStatus provenancePkg statusPkg
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
  have statusUnary : UnaryHistory statusRead :=
    unary_cont_closed terminalUnary localNameUnary terminalLocalNameStatus
  exact
    ⟨terminalUnary, statusUnary, dyadicStreamSource, sourceRegseqStream,
      streamSealRegseq, regseqTransportSeal, sealLocalNameInterface,
      interfaceRouteTerminal, terminalLocalNameStatus, provenancePkg, statusPkg,
      (cont_mutual_extension_right_tail_absurd.left interfaceRouteTerminal),
      (cont_mutual_extension_right_tail_absurd.right interfaceRouteTerminal)⟩

end BEDC.Derived.RealUp
