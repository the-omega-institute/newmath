import BEDC.Derived.DyadicIntervalCoverUp.PublicFiniteCoverExport
import BEDC.Derived.DyadicIntervalCoverUp.StandardBridgePremise

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverBridgeHandoff [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N endpointRead windowRead readbackRead coverRead sealRead
      subcoverRead namedRead publicRead coverBridgeRead sealBridgeRead bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg →
      Cont L U endpointRead →
        Cont W Q windowRead →
          Cont windowRead R readbackRead →
            Cont readbackRead V coverRead →
              Cont coverRead A sealRead →
                Cont endpointRead sealRead subcoverRead →
                  Cont subcoverRead N namedRead →
                    Cont namedRead P publicRead →
                      Cont M R coverBridgeRead →
                        Cont coverBridgeRead A sealBridgeRead →
                          Cont endpointRead sealBridgeRead bridgeRead →
                            PkgSig bundle publicRead pkg →
                              PkgSig bundle bridgeRead pkg →
                                SemanticNameCert
                                    (fun row : BHist => hsame row publicRead ∧
                                      UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row L ∨ hsame row U ∨ hsame row M ∨
                                        hsame row R ∨ hsame row V ∨ hsame row W ∨
                                          hsame row Q ∨ hsame row A ∨ hsame row H ∨
                                            hsame row C ∨ hsame row P ∨ hsame row N ∨
                                              hsame row publicRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont L U endpointRead ∧
                                        Cont W Q windowRead ∧
                                          Cont windowRead R readbackRead ∧
                                            Cont readbackRead V coverRead ∧
                                              Cont coverRead A sealRead ∧
                                                Cont endpointRead sealRead subcoverRead ∧
                                                  Cont subcoverRead N namedRead ∧
                                                    Cont namedRead P publicRead ∧
                                                      PkgSig bundle publicRead pkg)
                                    hsame ∧ UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro surface endpointRoute windowRoute readbackRoute coverRoute sealRoute subcoverRoute
    namedRoute publicRoute coverBridgeRoute sealBridgeRoute bridgeRoute publicPkg bridgePkg
  have publicExport :=
    DyadicIntervalCoverPublicFiniteCoverExport
      surface endpointRoute windowRoute readbackRoute coverRoute sealRoute subcoverRoute
      namedRoute publicRoute publicPkg
  have rows :
      UnaryHistory L ∧ UnaryHistory U ∧ UnaryHistory M ∧ UnaryHistory R ∧
        UnaryHistory V ∧ UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory A ∧
          UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
            PkgSig bundle P pkg :=
    ⟨surface.left, surface.right.left, surface.right.right.left,
      surface.right.right.right.left, surface.right.right.right.right.left,
      surface.right.right.right.right.right.left,
      surface.right.right.right.right.right.right.left,
      surface.right.right.right.right.right.right.right.left,
      surface.right.right.right.right.right.right.right.right.left,
      surface.right.right.right.right.right.right.right.right.right.left,
      surface.right.right.right.right.right.right.right.right.right.right.left,
      surface.right.right.right.right.right.right.right.right.right.right.right.left,
      surface.right.right.right.right.right.right.right.right.right.right.right.right.left⟩
  have bridgeExport :=
    DyadicIntervalCoverStandardBridgePremise
      rows endpointRoute coverBridgeRoute sealBridgeRoute bridgeRoute bridgePkg
  exact ⟨publicExport.left, bridgeExport.right.right.right.left⟩

end BEDC.Derived.DyadicIntervalCoverUp
