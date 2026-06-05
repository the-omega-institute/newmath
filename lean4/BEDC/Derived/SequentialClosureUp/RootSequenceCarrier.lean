import BEDC.Derived.SequentialClosureUp.SequenceLimitHandoff

namespace BEDC.Derived.SequentialClosureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem SequentialClosureRootSequenceCarrier [AskSetup] [PackageSetup]
    {topology metric source sequence limitRow tests windows regseq realSeal transport replay
      provenance nameCert sequenceRead windowRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialClosureCarrier topology metric source sequence limitRow tests windows regseq realSeal
        transport replay provenance nameCert bundle pkg →
      Cont source sequence sequenceRead →
        Cont sequenceRead windows windowRead →
          PkgSig bundle provenance pkg →
            PkgSig bundle nameCert pkg →
              hsame sequenceRead (append source sequence) ∧
                hsame windowRead (append sequenceRead windows) ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg := by
  -- BEDC touchpoint anchor: SequentialClosureCarrier BHist ProbeBundle Pkg Cont hsame
  intro _carrier sequenceRoute windowRoute provenancePkg namePkg
  exact ⟨sequenceRoute, windowRoute, provenancePkg, namePkg⟩

end BEDC.Derived.SequentialClosureUp
