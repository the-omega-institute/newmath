import BEDC.Derived.GeneratorAuditClosureUp

namespace BEDC.Derived.GeneratorAuditClosureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem GeneratorAuditClosureCarrier_substitution_shift_audit [AskSetup] [PackageSetup]
    {generator classifier accepted audit transport replay provenance localName acceptedRead auditRead
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GeneratorAuditClosureCarrier generator classifier accepted audit transport replay provenance
        localName bundle pkg →
      Cont generator classifier acceptedRead →
        Cont accepted audit auditRead →
          Cont auditRead replay consumerRead →
            PkgSig bundle consumerRead pkg →
              hsame acceptedRead accepted ∧ hsame auditRead audit ∧ hsame consumerRead audit ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
                  PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame
  intro carrier generatorRead auditReadRoute consumerReadRoute consumerPkg
  obtain ⟨_transportSelf, acceptedEmpty, replayEmpty, generatorAccepted, _acceptedReplay,
    provenancePkg, localNamePkg⟩ := carrier
  have acceptedReadAccepted : hsame acceptedRead accepted :=
    hsame_trans generatorRead generatorAccepted.symm
  have auditReadAudit : hsame auditRead audit := by
    cases acceptedEmpty
    exact auditReadRoute.trans (append_empty_left audit)
  have consumerReadAudit : hsame consumerRead audit := by
    have consumerReadAuditRead : hsame consumerRead auditRead := by
      cases replayEmpty
      exact consumerReadRoute.trans (append_empty_right auditRead)
    exact hsame_trans consumerReadAuditRead auditReadAudit
  exact
    ⟨acceptedReadAccepted, auditReadAudit, consumerReadAudit, provenancePkg, localNamePkg,
      consumerPkg⟩

end BEDC.Derived.GeneratorAuditClosureUp
