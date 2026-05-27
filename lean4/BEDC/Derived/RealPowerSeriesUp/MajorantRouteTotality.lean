import BEDC.Derived.RealPowerSeriesUp

namespace BEDC.Derived.RealPowerSeriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealPowerSeriesCarrier_majorant_route_totality [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N majorantRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont S M majorantRead ->
        Cont majorantRead E endpointRead ->
          PkgSig bundle majorantRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row majorantRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row M ∨ hsame row majorantRead ∨ Cont S M majorantRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle majorantRead pkg)
                hsame ∧
              UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory majorantRead ∧
                Cont R S M ∧ Cont S M majorantRead ∧
                  PkgSig bundle majorantRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier majorantRoute _endpointRoute majorantPkg
  obtain ⟨_AUnary, _ZUnary, _XUnary, _RUnary, _WUnary, SUnary, MUnary, _EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, _coefficientWindow, radiusMajorant,
    _majorantEndpoint, carrierPkg⟩ := carrier
  have majorantUnary : UnaryHistory majorantRead :=
    unary_cont_closed SUnary MUnary majorantRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row majorantRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row majorantRead ∨ Cont S M majorantRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle majorantRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro majorantRead ⟨hsame_refl majorantRead, majorantUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inl sourceRow.left)
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, carrierPkg, majorantPkg⟩
  }
  exact
    ⟨cert, SUnary, MUnary, majorantUnary, radiusMajorant, majorantRoute, majorantPkg⟩

end BEDC.Derived.RealPowerSeriesUp
