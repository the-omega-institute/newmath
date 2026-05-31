import BEDC.Derived.HausdorffSpaceUp.TasteGate

namespace BEDC.Derived.HausdorffSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HausdorffSpaceCarrier_open_neighborhood_classifier_transport [AskSetup] [PackageSetup]
    {T x y U V D M E H C P N T' x' y' U' V' D' M' E' separation separation'
      classifier classifier' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HausdorffSpaceCarrier T x y U V D M E H C P N bundle pkg ->
      HausdorffSpaceCarrier T' x' y' U' V' D' M' E' H C P N bundle pkg ->
        hsame T T' ->
          hsame U U' ->
            hsame V V' ->
              hsame D D' ->
                Cont U V separation ->
                  Cont U' V' separation' ->
                    Cont separation D classifier ->
                      Cont separation' D' classifier' ->
                        UnaryHistory U ∧ UnaryHistory V ∧ UnaryHistory D ∧
                          UnaryHistory separation ∧ UnaryHistory separation' ∧
                            UnaryHistory classifier ∧ UnaryHistory classifier' ∧
                              hsame separation separation' ∧ hsame classifier classifier' ∧
                                PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier carrier' _sameTopology sameOpenLeft sameOpenRight sameDisjoint
    separationRoute transportedSeparation classifierRoute transportedClassifier
  obtain ⟨_tUnary, _xUnary, _yUnary, uUnary, vUnary, dUnary, _mUnary, _eUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _pointRoute, _transportRoute, _disjointRoute,
    _metricRoute, provenancePkg⟩ := carrier
  obtain ⟨_tUnary', _xUnary', _yUnary', uUnary', vUnary', dUnary', _mUnary', _eUnary',
    _hUnary', _cUnary', _pUnary', _nUnary', _pointRoute', _transportRoute',
    _disjointRoute', _metricRoute', _provenancePkg'⟩ := carrier'
  have separationUnary : UnaryHistory separation :=
    unary_cont_closed uUnary vUnary separationRoute
  have transportedSeparationUnary : UnaryHistory separation' :=
    unary_cont_closed uUnary' vUnary' transportedSeparation
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed separationUnary dUnary classifierRoute
  have transportedClassifierUnary : UnaryHistory classifier' :=
    unary_cont_closed transportedSeparationUnary dUnary' transportedClassifier
  have separationStable : hsame separation separation' :=
    cont_respects_hsame sameOpenLeft sameOpenRight separationRoute transportedSeparation
  have classifierStable : hsame classifier classifier' :=
    cont_respects_hsame separationStable sameDisjoint classifierRoute transportedClassifier
  exact
    ⟨uUnary, vUnary, dUnary, separationUnary, transportedSeparationUnary, classifierUnary,
      transportedClassifierUnary, separationStable, classifierStable, provenancePkg⟩

end BEDC.Derived.HausdorffSpaceUp
