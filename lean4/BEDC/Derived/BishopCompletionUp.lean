import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BishopCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopCompletionCarrier_filter_compatibility [AskSetup] [PackageSetup]
    {R S D E F U H C P N F' : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (carrier :
      UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory E ∧
        UnaryHistory F ∧ UnaryHistory U ∧ UnaryHistory H ∧ UnaryHistory C ∧
          UnaryHistory P ∧ UnaryHistory N ∧ Cont S R D ∧ Cont D E F ∧ Cont F U C ∧
            PkgSig bundle P pkg)
    (sameFilter : Cont D E F') :
    hsame F F' ∧ UnaryHistory F ∧ UnaryHistory F' ∧ Cont S R D ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  obtain ⟨_rUnary, _sUnary, dUnary, eUnary, fUnary, _uUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, streamRoute, filterRoute, _universalRoute, pkgSig⟩ := carrier
  have sameFiniteFilter : hsame F F' :=
    cont_deterministic filterRoute sameFilter
  have fPrimeUnary : UnaryHistory F' :=
    unary_cont_closed dUnary eUnary sameFilter
  exact ⟨sameFiniteFilter, fUnary, fPrimeUnary, streamRoute, pkgSig⟩

theorem BishopCompletionCarrier_namecert_obligations [AskSetup] [PackageSetup]
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
        UnaryHistory realRead ∧ UnaryHistory filterRead ∧ UnaryHistory universalRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert UnaryHistory hsame
  intro carrier
  obtain ⟨rUnary, sUnary, dUnary, eUnary, fUnary, uUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, regularRoute, dyadicRoute, realRoute, filterRoute,
    universalRoute, provenancePkg, namePkg⟩ := carrier
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed sUnary rUnary regularRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed regularUnary dUnary dyadicRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed dyadicUnary eUnary realRoute
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed realUnary fUnary filterRoute
  have universalUnary : UnaryHistory universalRead :=
    unary_cont_closed filterUnary uUnary universalRoute
  have cert :
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
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro universalRead ⟨hsame_refl universalRead, universalUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, regularRoute, dyadicRoute, realRoute, filterRoute, universalRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, regularUnary, dyadicUnary, realUnary, filterUnary, universalUnary⟩

end BEDC.Derived.BishopCompletionUp
