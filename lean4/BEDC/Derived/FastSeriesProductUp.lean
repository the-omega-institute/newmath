import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.FastSeriesProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FastSeriesProductCarrier [AskSetup] [PackageSetup]
    (f g k w m t r e l c p n endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory f ∧ UnaryHistory g ∧ UnaryHistory k ∧ UnaryHistory w ∧
    UnaryHistory m ∧ UnaryHistory t ∧ UnaryHistory r ∧ UnaryHistory e ∧
      UnaryHistory l ∧ UnaryHistory c ∧ UnaryHistory p ∧ UnaryHistory n ∧
        UnaryHistory endpoint ∧ Cont f g k ∧ Cont k w m ∧ Cont m t r ∧
          Cont r e endpoint ∧ PkgSig bundle endpoint pkg

theorem FastSeriesProductCarrier_tail_bound_convolution [AskSetup] [PackageSetup]
    {f g k w m t r e l c p n endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastSeriesProductCarrier f g k w m t r e l c p n endpoint bundle pkg ->
      UnaryHistory k ∧ UnaryHistory w ∧ UnaryHistory m ∧ UnaryHistory t ∧
        Cont k w m ∧ Cont m t r ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  exact
    ⟨carrier.right.right.left,
      carrier.right.right.right.left,
      carrier.right.right.right.right.left,
      carrier.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right⟩

theorem FastSeriesProductCarrier_classifier_transport_exactness [AskSetup] [PackageSetup]
    {f g k w m t r e l c p n endpoint f' g' k' w' m' t' r' e' l' c' p' n' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastSeriesProductCarrier f g k w m t r e l c p n endpoint bundle pkg ->
      hsame f f' ->
        hsame g g' ->
          Cont f' g' k' ->
            hsame w w' ->
              Cont k' w' m' ->
                hsame t t' ->
                  Cont m' t' r' ->
                    hsame e e' ->
                      Cont r' e' endpoint ->
                        hsame l l' ->
                          hsame c c' ->
                            hsame p p' ->
                              hsame n n' ->
                                FastSeriesProductCarrier f' g' k' w' m' t' r' e'
                                    l' c' p' n' endpoint bundle pkg ∧
                                  hsame k k' ∧ hsame m m' ∧ hsame r r' := by
  intro carrier sameF sameG fgRow' sameW kwRow' sameT mtRow' sameE reRow'
    sameL sameC sameP sameN
  obtain ⟨fUnary, gUnary, kUnary, wUnary, mUnary, tUnary, rUnary, eUnary, lUnary,
    cUnary, pUnary, nUnary, endpointUnary, fgRow, kwRow, mtRow, reRow, pkgSig⟩ := carrier
  have sameK : hsame k k' :=
    cont_respects_hsame sameF sameG fgRow fgRow'
  have sameM : hsame m m' :=
    cont_respects_hsame sameK sameW kwRow kwRow'
  have sameR : hsame r r' :=
    cont_respects_hsame sameM sameT mtRow mtRow'
  have fUnary' : UnaryHistory f' := unary_transport fUnary sameF
  have gUnary' : UnaryHistory g' := unary_transport gUnary sameG
  have kUnary' : UnaryHistory k' := unary_transport kUnary sameK
  have wUnary' : UnaryHistory w' := unary_transport wUnary sameW
  have mUnary' : UnaryHistory m' := unary_transport mUnary sameM
  have tUnary' : UnaryHistory t' := unary_transport tUnary sameT
  have rUnary' : UnaryHistory r' := unary_transport rUnary sameR
  have eUnary' : UnaryHistory e' := unary_transport eUnary sameE
  have lUnary' : UnaryHistory l' := unary_transport lUnary sameL
  have cUnary' : UnaryHistory c' := unary_transport cUnary sameC
  have pUnary' : UnaryHistory p' := unary_transport pUnary sameP
  have nUnary' : UnaryHistory n' := unary_transport nUnary sameN
  exact
    ⟨⟨fUnary', gUnary', kUnary', wUnary', mUnary', tUnary', rUnary', eUnary',
      lUnary', cUnary', pUnary', nUnary', endpointUnary, fgRow', kwRow', mtRow',
      reRow', pkgSig⟩,
      sameK, sameM, sameR⟩

theorem FastSeriesProductCarrier_regseqrat_handoff [AskSetup] [PackageSetup]
    {f g k w m t r e l c p n endpoint handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastSeriesProductCarrier f g k w m t r e l c p n endpoint bundle pkg ->
      Cont w m handoff ->
        UnaryHistory r ∧ UnaryHistory handoff ∧ Cont m t r ∧ Cont w m handoff ∧
          PkgSig bundle endpoint pkg := by
  intro carrier handoffRow
  obtain ⟨_fUnary, _gUnary, _kUnary, wUnary, mUnary, _tUnary, rUnary, _eUnary,
    _lUnary, _cUnary, _pUnary, _nUnary, _endpointUnary, _fgRow, _kwRow, mtRow,
    _reRow, endpointPkg⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed wUnary mUnary handoffRow
  exact ⟨rUnary, handoffUnary, mtRow, handoffRow, endpointPkg⟩

theorem FastSeriesProductCarrier_real_seal_factorization [AskSetup] [PackageSetup]
    {f g k w m t r e l c p n endpoint handoff sealRowHist : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastSeriesProductCarrier f g k w m t r e l c p n endpoint bundle pkg ->
      Cont w m handoff ->
        Cont r e sealRowHist ->
          hsame sealRowHist endpoint ->
            UnaryHistory handoff ∧ UnaryHistory sealRowHist ∧ Cont w m handoff ∧
              Cont r e sealRowHist ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier handoffRow sealRow _sameSeal
  obtain ⟨_fUnary, _gUnary, _kUnary, wUnary, mUnary, _tUnary, rUnary, eUnary,
    _lUnary, _cUnary, _pUnary, _nUnary, _endpointUnary, _fgRow, _kwRow, _mtRow,
    _reRow, endpointPkg⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed wUnary mUnary handoffRow
  have sealUnary : UnaryHistory sealRowHist :=
    unary_cont_closed rUnary eUnary sealRow
  exact ⟨handoffUnary, sealUnary, handoffRow, sealRow, endpointPkg⟩

theorem FastSeriesProductUp_StdBridge [AskSetup] [PackageSetup]
    {f g k w m t r e l c p n endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastSeriesProductCarrier f g k w m t r e l c p n endpoint bundle pkg ->
      UnaryHistory f ∧ UnaryHistory g ∧ UnaryHistory k ∧ UnaryHistory w ∧
        UnaryHistory m ∧ UnaryHistory t ∧ UnaryHistory r ∧ UnaryHistory e ∧
          Cont f g k ∧ Cont k w m ∧ Cont m t r ∧ Cont r e endpoint ∧
            PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier
  obtain ⟨fUnary, gUnary, kUnary, wUnary, mUnary, tUnary, rUnary, eUnary,
    _lUnary, _cUnary, _pUnary, _nUnary, _endpointUnary, fgRow, kwRow, mtRow,
    reRow, endpointPkg⟩ := carrier
  exact
    ⟨fUnary, gUnary, kUnary, wUnary, mUnary, tUnary, rUnary, eUnary, fgRow,
      kwRow, mtRow, reRow, endpointPkg⟩

end BEDC.Derived.FastSeriesProductUp
