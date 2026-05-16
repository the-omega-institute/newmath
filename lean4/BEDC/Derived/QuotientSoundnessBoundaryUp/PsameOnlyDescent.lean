import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem QuotientSoundnessBoundary_psame_only_descent [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead transportRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg ->
      Cont v t refusalRead ->
        Cont t h transportRead ->
          Cont h c consumer ->
            PkgSig bundle refusalRead pkg ->
              PkgSig bundle transportRead pkg ->
                PkgSig bundle consumer pkg ->
                  hsame (append (append v t) h) (append v transportRead) ∧
                    hsame (append t h) transportRead ∧
                      hsame (append h c) consumer ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro _carrier _vTRefusal tHTransport hCConsumer _refusalPkg _transportPkg consumerPkg
  constructor
  · cases tHTransport
    exact append_assoc v t h
  · constructor
    · exact tHTransport.symm
    · exact ⟨hCConsumer.symm, consumerPkg⟩

end BEDC.Derived.QuotientSoundnessBoundaryUp
