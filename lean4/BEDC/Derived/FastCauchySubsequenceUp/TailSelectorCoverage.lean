import BEDC.Derived.FastCauchySubsequenceUp.NameCertObligations

namespace BEDC.Derived.FastCauchySubsequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem FastCauchySubsequenceTailSelectorCoverage [AskSetup] [PackageSetup]
    {source modulus selector fastRow regularRow windowRow realSeal transport replay provenance
      nameCert selectedTail regularTail sealedTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchySubsequenceCarrier source modulus selector fastRow regularRow windowRow realSeal
        transport replay provenance nameCert bundle pkg →
      Cont modulus selector selectedTail →
        Cont selectedTail regularRow regularTail →
          Cont regularTail realSeal sealedTail →
            PkgSig bundle provenance pkg →
              PkgSig bundle nameCert pkg →
                hsame selectedTail (append modulus selector) ∧
                  hsame regularTail (append selectedTail regularRow) ∧
                    hsame sealedTail (append regularTail realSeal) ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg := by
  -- BEDC touchpoint anchor: FastCauchySubsequenceCarrier BHist ProbeBundle Pkg Cont hsame
  intro _carrier selectedRoute regularRoute sealedRoute provenancePkg namePkg
  exact ⟨selectedRoute, regularRoute, sealedRoute, provenancePkg, namePkg⟩

end BEDC.Derived.FastCauchySubsequenceUp
