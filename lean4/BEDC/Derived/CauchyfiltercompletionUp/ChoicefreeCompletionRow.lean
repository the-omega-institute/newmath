import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_choicefree_completion_row [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name completionRead
      finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont readback sealRow completionRead →
        Cont completionRead provenance finalRead →
          PkgSig bundle finalRead pkg →
            UnaryHistory filter ∧ UnaryHistory windows ∧ UnaryHistory tolerance ∧
              UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory completionRead ∧
                UnaryHistory finalRead ∧ Cont filter windows tolerance ∧
                  Cont tolerance readback sealRow ∧ Cont readback sealRow completionRead ∧
                    Cont completionRead provenance finalRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle finalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet completionRoute finalRoute finalPkg
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed readbackUnary sealUnary completionRoute
  have finalUnary : UnaryHistory finalRead :=
    unary_cont_closed completionUnary provenanceUnary finalRoute
  exact
    ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary, completionUnary,
      finalUnary, filterWindows, toleranceReadback, completionRoute, finalRoute, provenancePkg,
      finalPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
