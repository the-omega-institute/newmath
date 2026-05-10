import BEDC.Derived.GaloisExtUp

namespace BEDC.Derived.GaloisExtUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.Derived.GaloisGroupUp

theorem GaloisExtUp_StdBridge [AskSetup] [PackageSetup]
    {fieldExt polynomial generator minimal simpleRoot sepProvenance separable normality
      separability classifier provenance endpoint automorphism action inverse automorphismLedger
      bridge : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GaloisExtSourcePacket fieldExt polynomial generator minimal simpleRoot sepProvenance
        separable normality separability classifier provenance endpoint bundle pkg ->
      GaloisGroupAutomorphismActionPacket fieldExt automorphism normality action separability
          inverse classifier provenance automorphismLedger endpoint bundle pkg ->
        Cont provenance automorphismLedger bridge ->
          hsame bridge (append provenance automorphismLedger) ∧ PkgSig bundle endpoint pkg := by
  intro sourcePacket _actionPacket bridgeRow
  exact And.intro bridgeRow sourcePacket.right.right.right.right.right.right

end BEDC.Derived.GaloisExtUp
