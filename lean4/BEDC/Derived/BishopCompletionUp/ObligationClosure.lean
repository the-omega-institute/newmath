import BEDC.Derived.BishopCompletionUp

namespace BEDC.Derived.BishopCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopCompletionCarrier_obligation_closure_package [AskSetup] [PackageSetup]
    {R S D E F U H C P N regularRead dyadicRead realRead filterRead
      universalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory E ∧
        UnaryHistory F ∧ UnaryHistory U ∧ UnaryHistory H ∧ UnaryHistory C ∧
          UnaryHistory P ∧ UnaryHistory N ∧ Cont S R regularRead ∧
            Cont regularRead D dyadicRead ∧ Cont dyadicRead E realRead ∧
              Cont realRead F filterRead ∧ Cont filterRead U universalRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg) ->
      SemanticNameCert
          (fun row : BHist => hsame row universalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row R ∨ hsame row D ∨ hsame row E ∨ hsame row F ∨
              hsame row U ∨ hsame row universalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S R regularRead ∧ Cont regularRead D dyadicRead ∧
              Cont dyadicRead E realRead ∧ Cont realRead F filterRead ∧
                Cont filterRead U universalRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle N pkg)
          hsame ∧ UnaryHistory regularRead ∧ UnaryHistory dyadicRead ∧
        UnaryHistory realRead ∧ UnaryHistory filterRead ∧ UnaryHistory universalRead ∧
          Cont S R regularRead ∧ Cont regularRead D dyadicRead ∧
            Cont dyadicRead E realRead ∧ Cont realRead F filterRead ∧
              Cont filterRead U universalRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg SemanticNameCert UnaryHistory hsame
  intro carrier
  have obligations := BishopCompletionCarrier_namecert_obligations carrier
  obtain ⟨cert, regularUnary, dyadicUnary, realUnary, filterUnary, universalUnary⟩ :=
    obligations
  obtain ⟨_rUnary, _sUnary, _dUnary, _eUnary, _fUnary, _uUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, regularRoute, dyadicRoute, realRoute, filterRoute,
    universalRoute, provenancePkg, namePkg⟩ := carrier
  exact
    ⟨cert, regularUnary, dyadicUnary, realUnary, filterUnary, universalUnary,
      regularRoute, dyadicRoute, realRoute, filterRoute, universalRoute, provenancePkg,
      namePkg⟩

end BEDC.Derived.BishopCompletionUp
