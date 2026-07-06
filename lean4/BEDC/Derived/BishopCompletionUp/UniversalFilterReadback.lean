import BEDC.Derived.BishopCompletionUp

namespace BEDC.Derived.BishopCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopCompletionCarrier_universal_filter_readback [AskSetup] [PackageSetup]
    {R S D E F U H C P N F' universalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (carrier :
      UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory E ∧
        UnaryHistory F ∧ UnaryHistory U ∧ UnaryHistory H ∧ UnaryHistory C ∧
          UnaryHistory P ∧ UnaryHistory N ∧ Cont S R D ∧ Cont D E F ∧
            Cont F U C ∧ PkgSig bundle P pkg)
    (sameFilter : Cont D E F') (universalRoute : Cont F' U universalRead) :
    hsame F F' ∧ UnaryHistory F' ∧ UnaryHistory universalRead ∧
      Cont F' U universalRead ∧ Cont S R D ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory hsame
  obtain ⟨sameFiniteFilter, _fUnary, fPrimeUnary, streamRoute, pkgSig⟩ :=
    BishopCompletionCarrier_filter_compatibility carrier sameFilter
  obtain ⟨_rUnary, _sUnary, _dUnary, _eUnary, _fUnaryCarrier, uUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _streamRouteCarrier, _filterRoute,
      _universalRouteCarrier, _pkgSigCarrier⟩ := carrier
  have universalReadUnary : UnaryHistory universalRead :=
    unary_cont_closed fPrimeUnary uUnary universalRoute
  exact ⟨sameFiniteFilter, fPrimeUnary, universalReadUnary, universalRoute, streamRoute, pkgSig⟩

theorem BishopCompletionCarrier_namecert_universal_ledger_readback [AskSetup] [PackageSetup]
    {R S D E F U H C P N regularRead dyadicRead realRead filterRead
      universalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory E ∧
        UnaryHistory F ∧ UnaryHistory U ∧ UnaryHistory H ∧ UnaryHistory C ∧
          UnaryHistory P ∧ UnaryHistory N ∧ Cont S R regularRead ∧
            Cont regularRead D dyadicRead ∧ Cont dyadicRead E realRead ∧
              Cont realRead F filterRead ∧ Cont filterRead U universalRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg) →
      ∃ row : BHist,
        (UnaryHistory row ∧ Cont S R regularRead ∧ Cont regularRead D dyadicRead ∧
            Cont dyadicRead E realRead ∧ Cont realRead F filterRead ∧
              Cont filterRead U universalRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle N pkg) ∧
          hsame row universalRead ∧ UnaryHistory universalRead ∧
            Cont filterRead U universalRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist Cont NameCert PkgSig SemanticNameCert UnaryHistory hsame
  intro carrier
  obtain ⟨cert, _regularUnary, _dyadicUnary, _realUnary, _filterUnary, universalUnary⟩ :=
    BishopCompletionCarrier_namecert_obligations carrier
  have sourceUniversal : hsame universalRead universalRead ∧ UnaryHistory universalRead :=
    ⟨hsame_refl universalRead, universalUnary⟩
  have ledgerUniversal :=
    cert.ledger_sound sourceUniversal
  have ledgerUniversalCopy := ledgerUniversal
  obtain ⟨_universalLedgerUnary, _regularRoute, _dyadicRoute, _realRoute, _filterRoute,
    universalRoute, provenancePkg, _namePkg⟩ := ledgerUniversal
  exact
    ⟨universalRead, ledgerUniversalCopy, hsame_refl universalRead, universalUnary,
      universalRoute, provenancePkg⟩

end BEDC.Derived.BishopCompletionUp
