import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem RealupOpenPhaseFourFacePullback [AskSetup] [PackageSetup]
    {dyadicA streamA regseqA sealA dyadicB streamB regseqB sealB sourceA sourceB
      streamReadA streamReadB regseqReadA regseqReadB sealReadA sealReadB : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont dyadicA streamA sourceA ->
      Cont dyadicB streamB sourceB ->
        Cont sourceA regseqA streamReadA ->
          Cont sourceB regseqB streamReadB ->
            Cont streamReadA sealA regseqReadA ->
              Cont streamReadB sealB regseqReadB ->
                Cont regseqReadA sealA sealReadA ->
                  Cont regseqReadB sealB sealReadB ->
                    hsame dyadicA dyadicB ->
                      hsame streamA streamB ->
                        hsame regseqA regseqB ->
                          hsame sealA sealB ->
                            PkgSig bundle sealReadA pkg ->
                              PkgSig bundle sealReadB pkg ->
                                hsame sourceA sourceB ∧ hsame streamReadA streamReadB ∧
                                  hsame regseqReadA regseqReadB ∧
                                    hsame sealReadA sealReadB ∧
                                      PkgSig bundle sealReadA pkg ∧
                                        PkgSig bundle sealReadB pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame
  intro sourceRouteA sourceRouteB streamRouteA streamRouteB regseqRouteA regseqRouteB
    sealRouteA sealRouteB sameDyadic sameStream sameRegseq sameSeal sealPkgA sealPkgB
  have sameSource : hsame sourceA sourceB :=
    cont_respects_hsame sameDyadic sameStream sourceRouteA sourceRouteB
  have sameStreamRead : hsame streamReadA streamReadB :=
    cont_respects_hsame sameSource sameRegseq streamRouteA streamRouteB
  have sameRegseqRead : hsame regseqReadA regseqReadB :=
    cont_respects_hsame sameStreamRead sameSeal regseqRouteA regseqRouteB
  have sameSealRead : hsame sealReadA sealReadB :=
    cont_respects_hsame sameRegseqRead sameSeal sealRouteA sealRouteB
  exact ⟨sameSource, sameStreamRead, sameRegseqRead, sameSealRead, sealPkgA, sealPkgB⟩

end BEDC.Derived.RealUp
