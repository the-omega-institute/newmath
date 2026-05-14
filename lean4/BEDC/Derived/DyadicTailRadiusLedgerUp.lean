import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicTailRadiusLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicTailRadiusLedgerCarrier [AskSetup] [PackageSetup]
    (precision tailWindow streamWindows dyadicReadback regSeqHandoff realSeal transport routes
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory precision ∧ UnaryHistory tailWindow ∧ UnaryHistory streamWindows ∧
    UnaryHistory dyadicReadback ∧ UnaryHistory regSeqHandoff ∧ UnaryHistory realSeal ∧
      UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont precision tailWindow streamWindows ∧ Cont streamWindows dyadicReadback routes ∧
          Cont routes regSeqHandoff realSeal ∧ Cont realSeal localName provenance ∧
            PkgSig bundle provenance pkg

theorem DyadicTailRadiusLedgerCarrier_window_route_scope [AskSetup] [PackageSetup]
    {precision tailWindow streamWindows dyadicReadback regSeqHandoff realSeal transport routes
      provenance localName precision' tailWindow' streamWindows' dyadicReadback' regSeqHandoff'
      realSeal' transport' routes' provenance' localName' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicTailRadiusLedgerCarrier precision tailWindow streamWindows dyadicReadback
        regSeqHandoff realSeal transport routes provenance localName bundle pkg →
      hsame precision precision' →
        hsame tailWindow tailWindow' →
          hsame dyadicReadback dyadicReadback' →
            hsame regSeqHandoff regSeqHandoff' →
              hsame localName localName' →
                Cont precision' tailWindow' streamWindows' →
                  Cont streamWindows' dyadicReadback' routes' →
                    Cont routes' regSeqHandoff' realSeal' →
                      Cont realSeal' localName' provenance' →
                        PkgSig bundle provenance' pkg →
                          DyadicTailRadiusLedgerCarrier precision' tailWindow' streamWindows'
                              dyadicReadback' regSeqHandoff' realSeal' transport' routes'
                              provenance' localName' bundle pkg ∧
                            hsame streamWindows streamWindows' ∧ hsame routes routes' ∧
                              hsame realSeal realSeal' ∧ hsame provenance provenance' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig
  intro carrier samePrecision sameTailWindow sameDyadicReadback sameRegSeqHandoff
    sameLocalName precisionTailWindow' streamWindowsDyadicReadback' routesRegSeqHandoff'
    realSealLocalName' pkgSig'
  obtain ⟨precisionUnary, tailWindowUnary, _streamWindowsUnary, dyadicReadbackUnary,
    regSeqHandoffUnary, _realSealUnary, _routesUnary, _provenanceUnary, localNameUnary,
    precisionTailWindow, streamWindowsDyadicReadback, routesRegSeqHandoff,
    realSealLocalName, _pkgSig⟩ := carrier
  have precisionUnary' : UnaryHistory precision' :=
    unary_transport precisionUnary samePrecision
  have tailWindowUnary' : UnaryHistory tailWindow' :=
    unary_transport tailWindowUnary sameTailWindow
  have dyadicReadbackUnary' : UnaryHistory dyadicReadback' :=
    unary_transport dyadicReadbackUnary sameDyadicReadback
  have regSeqHandoffUnary' : UnaryHistory regSeqHandoff' :=
    unary_transport regSeqHandoffUnary sameRegSeqHandoff
  have localNameUnary' : UnaryHistory localName' :=
    unary_transport localNameUnary sameLocalName
  have streamWindowsUnary' : UnaryHistory streamWindows' :=
    unary_cont_closed precisionUnary' tailWindowUnary' precisionTailWindow'
  have routesUnary' : UnaryHistory routes' :=
    unary_cont_closed streamWindowsUnary' dyadicReadbackUnary' streamWindowsDyadicReadback'
  have realSealUnary' : UnaryHistory realSeal' :=
    unary_cont_closed routesUnary' regSeqHandoffUnary' routesRegSeqHandoff'
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed realSealUnary' localNameUnary' realSealLocalName'
  have sameStreamWindows : hsame streamWindows streamWindows' :=
    cont_respects_hsame samePrecision sameTailWindow precisionTailWindow precisionTailWindow'
  have sameRoutes : hsame routes routes' :=
    cont_respects_hsame sameStreamWindows sameDyadicReadback streamWindowsDyadicReadback
      streamWindowsDyadicReadback'
  have sameRealSeal : hsame realSeal realSeal' :=
    cont_respects_hsame sameRoutes sameRegSeqHandoff routesRegSeqHandoff
      routesRegSeqHandoff'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameRealSeal sameLocalName realSealLocalName realSealLocalName'
  exact
    ⟨⟨precisionUnary', tailWindowUnary', streamWindowsUnary', dyadicReadbackUnary',
        regSeqHandoffUnary', realSealUnary', routesUnary', provenanceUnary',
        localNameUnary', precisionTailWindow', streamWindowsDyadicReadback',
        routesRegSeqHandoff', realSealLocalName', pkgSig'⟩,
      sameStreamWindows, sameRoutes, sameRealSeal, sameProvenance⟩

end BEDC.Derived.DyadicTailRadiusLedgerUp
