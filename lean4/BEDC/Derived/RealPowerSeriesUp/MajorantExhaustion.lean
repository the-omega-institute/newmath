import BEDC.Derived.RealPowerSeriesUp

namespace BEDC.Derived.RealPowerSeriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealPowerSeriesCarrier_majorant_exhaustion [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N majorantRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont S M majorantRead ->
        Cont majorantRead E endpointRead ->
          PkgSig bundle majorantRead pkg ->
            PkgSig bundle endpointRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row M ∨ hsame row majorantRead ∨ hsame row endpointRead)
                  (fun row : BHist =>
                    hsame row S ∨ hsame row M ∨ hsame row E ∨ hsame row majorantRead ∨
                      hsame row endpointRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧
                      (PkgSig bundle majorantRead pkg ∨ PkgSig bundle endpointRead pkg))
                  hsame ∧
                UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory majorantRead ∧
                  UnaryHistory endpointRead ∧ Cont R S M ∧ Cont S M majorantRead ∧
                    Cont majorantRead E endpointRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier majorantRoute endpointRoute majorantPkg endpointPkg
  obtain ⟨_AUnary, _ZUnary, _XUnary, _RUnary, _WUnary, SUnary, MUnary, EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, _coefficientWindow, radiusMajorant,
    _majorantEndpoint, _pkgSig⟩ := carrier
  have majorantReadUnary : UnaryHistory majorantRead :=
    unary_cont_closed SUnary MUnary majorantRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed majorantReadUnary EUnary endpointRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row M ∨ hsame row majorantRead ∨ hsame row endpointRead)
          (fun row : BHist =>
            hsame row S ∨ hsame row M ∨ hsame row E ∨ hsame row majorantRead ∨
              hsame row endpointRead)
          (fun row : BHist =>
            UnaryHistory row ∧
              (PkgSig bundle majorantRead pkg ∨ PkgSig bundle endpointRead pkg))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro M (Or.inl (hsame_refl M))
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
        intro row other sameRows source
        cases source with
        | inl sameM =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameM)
        | inr rest =>
            cases rest with
            | inl sameMajorant =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameMajorant))
            | inr sameEndpoint =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameEndpoint))
    }
    pattern_sound := by
      intro row source
      cases source with
      | inl sameM =>
          exact Or.inr (Or.inl sameM)
      | inr rest =>
          cases rest with
          | inl sameMajorant =>
              exact Or.inr (Or.inr (Or.inr (Or.inl sameMajorant)))
          | inr sameEndpoint =>
              exact Or.inr (Or.inr (Or.inr (Or.inr sameEndpoint)))
    ledger_sound := by
      intro row source
      cases source with
      | inl sameM =>
          exact
            ⟨unary_transport MUnary (hsame_symm sameM), Or.inl majorantPkg⟩
      | inr rest =>
          cases rest with
          | inl sameMajorant =>
              exact
                ⟨unary_transport majorantReadUnary (hsame_symm sameMajorant),
                  Or.inl majorantPkg⟩
          | inr sameEndpoint =>
              exact
                ⟨unary_transport endpointReadUnary (hsame_symm sameEndpoint),
                  Or.inr endpointPkg⟩
  }
  exact
    ⟨cert, SUnary, MUnary, majorantReadUnary, endpointReadUnary, radiusMajorant,
      majorantRoute, endpointRoute⟩

end BEDC.Derived.RealPowerSeriesUp
