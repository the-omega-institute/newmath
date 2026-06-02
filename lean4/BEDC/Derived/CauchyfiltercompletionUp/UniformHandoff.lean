import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_uniform_handoff [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name uniformRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont sealRow provenance uniformRead →
        Cont uniformRead name publicRead →
          PkgSig bundle publicRead pkg →
            UnaryHistory uniformRead ∧ UnaryHistory publicRead ∧
              Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
                Cont sealRow provenance uniformRead ∧ Cont uniformRead name publicRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet sealUniform uniformPublic publicPkg
  obtain ⟨_filterUnary, _windowsUnary, _toleranceUnary, _readbackUnary, sealUnary,
    _transportUnary, _replayUnary, provenanceUnary, nameUnary, filterWindows,
    toleranceReadback, _transportReplay, provenancePkg, namePkg⟩ := packet
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed sealUnary provenanceUnary sealUniform
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed uniformUnary nameUnary uniformPublic
  exact
    ⟨uniformUnary, publicUnary, filterWindows, toleranceReadback, sealUniform, uniformPublic,
      provenancePkg, namePkg, publicPkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
