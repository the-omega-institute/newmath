import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def regular_cauchy_criterion_carrier_namecert_obligations_carrier [AskSetup] [PackageSetup]
    (stream readback modulus dyadic criterion convergence realBoundary transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory stream ∧ UnaryHistory readback ∧ UnaryHistory modulus ∧
    UnaryHistory dyadic ∧ UnaryHistory criterion ∧ UnaryHistory convergence ∧
      UnaryHistory realBoundary ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle localName pkg

theorem RegularCauchyCriterionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {stream readback modulus dyadic criterion convergence realBoundary transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    regular_cauchy_criterion_carrier_namecert_obligations_carrier
        stream readback modulus dyadic criterion convergence
        realBoundary transport replay provenance localName bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row localName ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream ∨ hsame row readback ∨ hsame row modulus ∨
              hsame row dyadic ∨ hsame row criterion ∨ hsame row convergence ∨
                hsame row realBoundary ∨ hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame ∧
        PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier
  obtain ⟨_streamUnary, _readbackUnary, _modulusUnary, _dyadicUnary, _criterionUnary,
    _convergenceUnary, _realBoundaryUnary, _transportUnary, _replayUnary, _provenanceUnary,
    localNameUnary, provenancePkg, localNamePkg⟩ := carrier
  have localSource :
      (fun row : BHist => hsame row localName ∧ UnaryHistory row) localName := by
    exact ⟨hsame_refl localName, localNameUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localName ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream ∨ hsame row readback ∨ hsame row modulus ∨
              hsame row dyadic ∨ hsame row criterion ∨ hsame row convergence ∨
                hsame row realBoundary ∨ hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localName localSource
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, provenancePkg, localNamePkg⟩

theorem RegularCauchyCriterionWindowExtraction [AskSetup] [PackageSetup]
    {S R M D Q V A H C P N streamWindow toleranceWindow criterionRead
      boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    regular_cauchy_criterion_carrier_namecert_obligations_carrier
        S R M D Q V A H C P N bundle pkg ->
      Cont S R streamWindow ->
        Cont M D toleranceWindow ->
          Cont toleranceWindow Q criterionRead ->
            Cont criterionRead V boundaryRead ->
              PkgSig bundle boundaryRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row S ∨ hsame row R ∨ hsame row M ∨ hsame row D ∨
                        hsame row Q ∨ hsame row V ∨ hsame row streamWindow ∨
                          hsame row toleranceWindow ∨ hsame row criterionRead ∨
                            hsame row boundaryRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont S R streamWindow ∧
                        Cont M D toleranceWindow ∧ Cont toleranceWindow Q criterionRead ∧
                          Cont criterionRead V boundaryRead ∧
                            PkgSig bundle boundaryRead pkg)
                    hsame ∧
                  UnaryHistory streamWindow ∧ UnaryHistory toleranceWindow ∧
                    UnaryHistory criterionRead ∧ UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier streamRoute toleranceRoute criterionRoute boundaryRoute boundaryPkg
  obtain ⟨sUnary, rUnary, mUnary, dUnary, qUnary, vUnary, _aUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _provenancePkg, _localNamePkg⟩ := carrier
  have streamUnary : UnaryHistory streamWindow :=
    unary_cont_closed sUnary rUnary streamRoute
  have toleranceUnary : UnaryHistory toleranceWindow :=
    unary_cont_closed mUnary dUnary toleranceRoute
  have criterionUnary : UnaryHistory criterionRead :=
    unary_cont_closed toleranceUnary qUnary criterionRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed criterionUnary vUnary boundaryRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row R ∨ hsame row M ∨ hsame row D ∨ hsame row Q ∨
              hsame row V ∨ hsame row streamWindow ∨ hsame row toleranceWindow ∨
                hsame row criterionRead ∨ hsame row boundaryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S R streamWindow ∧ Cont M D toleranceWindow ∧
              Cont toleranceWindow Q criterionRead ∧ Cont criterionRead V boundaryRead ∧
                PkgSig bundle boundaryRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro boundaryRead ⟨hsame_refl boundaryRead, boundaryUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, streamRoute, toleranceRoute, criterionRoute, boundaryRoute,
          boundaryPkg⟩
  }
  exact ⟨cert, streamUnary, toleranceUnary, criterionUnary, boundaryUnary⟩

end BEDC.Derived.RegularCauchyCriterionUp
