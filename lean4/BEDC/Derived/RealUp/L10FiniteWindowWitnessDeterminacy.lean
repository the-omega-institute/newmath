import BEDC.Derived.RealUp.L10DependencyLattice

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealL10FiniteWindowWitnessDeterminacy [AskSetup] [PackageSetup]
    {dyadic stream regseq sealRow transport route provenance localName sourceRoute streamRoute
      regseqRoute sealRoute interfaceRead finiteWindowWitness : BHist}
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
                              Cont interfaceRead stream finiteWindowWitness ->
                                PkgSig bundle provenance pkg ->
                                  PkgSig bundle finiteWindowWitness pkg ->
                                    UnaryHistory sourceRoute ∧ UnaryHistory streamRoute ∧
                                      UnaryHistory regseqRoute ∧ UnaryHistory sealRoute ∧
                                        UnaryHistory interfaceRead ∧
                                          UnaryHistory finiteWindowWitness ∧
                                            Cont dyadic stream sourceRoute ∧
                                              Cont sourceRoute regseq streamRoute ∧
                                                Cont streamRoute sealRow regseqRoute ∧
                                                  Cont regseqRoute transport sealRoute ∧
                                                    Cont sealRoute localName interfaceRead ∧
                                                      Cont interfaceRead stream
                                                        finiteWindowWitness ∧
                                                        PkgSig bundle provenance pkg ∧
                                                          PkgSig bundle
                                                            finiteWindowWitness pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro dyadicUnary streamUnary regseqUnary sealUnary transportUnary _routeUnary
    _provenanceUnary localNameUnary dyadicStreamSource sourceRegseqStream
    streamSealRegseq regseqTransportSeal sealLocalNameInterface interfaceStreamWindow
    provenancePkg finiteWindowPkg
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
  have finiteWindowUnary : UnaryHistory finiteWindowWitness :=
    unary_cont_closed interfaceUnary streamUnary interfaceStreamWindow
  exact
    ⟨sourceUnary, streamRouteUnary, regseqRouteUnary, sealRouteUnary, interfaceUnary,
      finiteWindowUnary, dyadicStreamSource, sourceRegseqStream, streamSealRegseq,
      regseqTransportSeal, sealLocalNameInterface, interfaceStreamWindow, provenancePkg,
      finiteWindowPkg⟩

end BEDC.Derived.RealUp
