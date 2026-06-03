import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionRootSiblingDependencyRoute [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name sourceRead sealRead
      rootRead completionRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont filter windows sourceRead →
        Cont sourceRead tolerance sealRead →
          Cont filter readback rootRead →
            Cont rootRead sealRow completionRead →
              Cont completionRead provenance publicRead →
                PkgSig bundle sealRead pkg →
                  PkgSig bundle publicRead pkg →
                    UnaryHistory sourceRead ∧ UnaryHistory sealRead ∧ UnaryHistory rootRead ∧
                      UnaryHistory completionRead ∧ UnaryHistory publicRead ∧
                        Cont filter windows sourceRead ∧ Cont sourceRead tolerance sealRead ∧
                          Cont filter readback rootRead ∧
                            Cont rootRead sealRow completionRead ∧
                              Cont completionRead provenance publicRead ∧
                                PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg ∧
                                  PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet sourceRoute sealRoute rootRoute completionRoute publicRoute sealPkg publicPkg
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, provenanceUnary, _nameUnary, _filterWindows,
    _toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed filterUnary windowsUnary sourceRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed sourceUnary toleranceUnary sealRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed filterUnary readbackUnary rootRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed rootUnary sealUnary completionRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed completionUnary provenanceUnary publicRoute
  exact
    ⟨sourceUnary, sealReadUnary, rootUnary, completionUnary, publicUnary, sourceRoute, sealRoute,
      rootRoute, completionRoute, publicRoute, provenancePkg, sealPkg, publicPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
