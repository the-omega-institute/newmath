import BEDC.Derived.CauchyNetCompletionUp.MooreSmithHandoff

namespace BEDC.Derived.CauchyNetCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyNetCompletionSeparatedComparisonExhaustion [AskSetup] [PackageSetup]
    {D W Q M U S R A H C P N boundaryRead comparisonRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyNetCompletionCarrier D W Q M U S R A H C P N bundle pkg ->
      Cont D W boundaryRead ->
        Cont boundaryRead S comparisonRead ->
          PkgSig bundle P pkg ->
            PkgSig bundle N pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row comparisonRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row D ∨ hsame row W ∨ hsame row S ∨ hsame row comparisonRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont D W boundaryRead ∧
                      Cont boundaryRead S comparisonRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle N pkg)
                  hsame ∧ UnaryHistory boundaryRead ∧
                UnaryHistory comparisonRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier boundaryRoute comparisonRoute provenancePkg localNamePkg
  obtain ⟨unaryD, unaryW, _unaryQ, _unaryM, _unaryU, unaryS, _unaryR, _unaryA,
    _unaryH, _unaryC, _carrierProvenanceUnary, _carrierNameUnary, _carrierBoundaryRoute,
      _carrierMooreRoute, _carrierUniformRoute, _carrierSealRoute, _carrierPkgP,
        _carrierPkgN⟩ := carrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryD unaryW boundaryRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed boundaryUnary unaryS comparisonRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row comparisonRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row S ∨ hsame row comparisonRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D W boundaryRead ∧
              Cont boundaryRead S comparisonRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro comparisonRead ⟨hsame_refl comparisonRead, comparisonUnary⟩
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, boundaryRoute, comparisonRoute, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, boundaryUnary, comparisonUnary⟩

end BEDC.Derived.CauchyNetCompletionUp
