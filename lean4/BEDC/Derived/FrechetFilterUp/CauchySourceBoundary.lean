import BEDC.Derived.FrechetFilterUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.FrechetFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FrechetFilterCauchySourceBoundary [AskSetup] [PackageSetup]
    {U T S M B Q R A H C P N cauchySource namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FrechetFilterCarrier U T S M B Q R A H C P N bundle pkg ->
      Cont U T cauchySource ->
        Cont cauchySource Q namedRead ->
          PkgSig bundle P pkg ->
            PkgSig bundle namedRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row U ∨ hsame row T ∨ hsame row S ∨ hsame row M ∨
                      hsame row B ∨ hsame row Q ∨ hsame row namedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont U T cauchySource ∧
                      Cont cauchySource Q namedRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle namedRead pkg)
                  hsame ∧
                UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier cauchyRoute namedRoute provenancePkg namedPkg
  obtain ⟨uUnary, tUnary, _sUnary, _mUnary, _bUnary, qUnary, _rUnary, _aUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _tailRoute, _scheduleRoute, _filterRoute,
    _sealRoute, _carrierProvenance, _carrierName⟩ := carrier
  have cauchyUnary : UnaryHistory cauchySource :=
    unary_cont_closed uUnary tUnary cauchyRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed cauchyUnary qUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row T ∨ hsame row S ∨ hsame row M ∨ hsame row B ∨
              hsame row Q ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont U T cauchySource ∧
              Cont cauchySource Q namedRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, cauchyRoute, namedRoute, provenancePkg, namedPkg⟩
  }
  exact ⟨cert, namedUnary⟩

end BEDC.Derived.FrechetFilterUp
