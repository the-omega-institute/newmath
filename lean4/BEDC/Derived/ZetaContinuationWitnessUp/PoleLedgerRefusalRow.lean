import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem ZetaContinuationWitnessPacket_pole_ledger_refusal_row
    [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      poleRead authRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
        transports routes provenance name bundle pkg →
      Cont pole zeroLedger poleRead →
        Cont transports routes authRead →
          PkgSig bundle authRead pkg →
            hsame poleRead gamma ∧ Cont transports routes provenance ∧
              PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle authRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame PkgSig
  intro packet poleRoute authRoute authPkg
  obtain ⟨_basicAnalytic, _analyticTransport, poleGamma, transportProvenance, namePkg,
    provenancePkg⟩ := packet
  have poleSame : hsame poleRead gamma :=
    cont_deterministic poleRoute poleGamma
  exact ⟨poleSame, transportProvenance, namePkg, provenancePkg, authPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
