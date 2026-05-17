import BEDC.Derived.RealUp

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

end BEDC.Derived.RealUp
