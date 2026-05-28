import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_basis_separated_reflector [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name separatedRead
      reflectorRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont sealRow transport separatedRead →
        Cont separatedRead replay reflectorRead →
          PkgSig bundle reflectorRead pkg →
            UnaryHistory filter ∧ UnaryHistory windows ∧ UnaryHistory tolerance ∧
              UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory separatedRead ∧
                UnaryHistory reflectorRead ∧ Cont filter windows tolerance ∧
                  Cont tolerance readback sealRow ∧ Cont sealRow transport separatedRead ∧
                    Cont separatedRead replay reflectorRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle reflectorRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet separatedRoute reflectorRoute reflectorPkg
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    transportUnary, replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed sealUnary transportUnary separatedRoute
  have reflectorUnary : UnaryHistory reflectorRead :=
    unary_cont_closed separatedUnary replayUnary reflectorRoute
  exact
    ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary, separatedUnary,
      reflectorUnary, filterWindows, toleranceReadback, separatedRoute, reflectorRoute,
      provenancePkg, reflectorPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
