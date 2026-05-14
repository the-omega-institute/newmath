import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicTailRadiusLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem DyadicTailRadiusLedgerCarrier_tail_budget_coverage [AskSetup] [PackageSetup]
    {precision tailWindow streamWindows dyadicReadback regSeqHandoff realSeal transport routes
      provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicTailRadiusLedgerCarrier precision tailWindow streamWindows dyadicReadback
        regSeqHandoff realSeal transport routes provenance localName bundle pkg →
      UnaryHistory precision ∧ UnaryHistory tailWindow ∧ UnaryHistory streamWindows ∧
        UnaryHistory dyadicReadback ∧ Cont precision tailWindow streamWindows ∧
          Cont streamWindows dyadicReadback routes ∧
            SemanticNameCert
              (fun row : BHist => hsame row dyadicReadback ∧ UnaryHistory row)
              (fun row : BHist => hsame row dyadicReadback)
              (fun row : BHist => hsame row dyadicReadback ∧ PkgSig bundle provenance pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont SemanticNameCert hsame
  intro carrier
  obtain ⟨precisionUnary, tailWindowUnary, streamWindowsUnary, dyadicReadbackUnary,
    _regSeqHandoffUnary, _realSealUnary, _routesUnary, _provenanceUnary, _localNameUnary,
    precisionTailWindow, streamWindowsDyadicReadback, _routesRegSeqHandoff,
    _realSealLocalName, pkgSig⟩ := carrier
  have sourceDyadicReadback :
      (fun row : BHist => hsame row dyadicReadback ∧ UnaryHistory row) dyadicReadback := by
    exact And.intro (hsame_refl dyadicReadback) dyadicReadbackUnary
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row dyadicReadback ∧ UnaryHistory row)
        (fun row : BHist => hsame row dyadicReadback)
        (fun row : BHist => hsame row dyadicReadback ∧ PkgSig bundle provenance pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro dyadicReadback sourceDyadicReadback
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row other same source
          exact And.intro (hsame_trans (hsame_symm same) source.left)
            (unary_transport source.right same)
      }
      pattern_sound := by
        intro _row source
        exact source.left
      ledger_sound := by
        intro _row source
        exact And.intro source.left pkgSig
    }
  exact
    ⟨precisionUnary, tailWindowUnary, streamWindowsUnary, dyadicReadbackUnary,
      precisionTailWindow, streamWindowsDyadicReadback, cert⟩

end BEDC.Derived.DyadicTailRadiusLedgerUp
