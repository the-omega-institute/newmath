import BEDC.Derived.CauchyNetCompletionUp.DirectedWindowCofinalRestriction

namespace BEDC.Derived.CauchyNetCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyNetCompletionDirectedWindowRefinementFunctoriality [AskSetup] [PackageSetup]
    {D W Q M U S R A H C P N restrictedD restrictedW restrictedBoundary
      restrictedRequest refinedD refinedW refinedBoundary refinedRequest : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyNetCompletionCarrier D W Q M U S R A H C P N bundle pkg ->
      UnaryHistory restrictedD ->
        UnaryHistory restrictedW ->
          Cont restrictedD restrictedW restrictedBoundary ->
            Cont restrictedBoundary Q restrictedRequest ->
              UnaryHistory refinedD ->
                UnaryHistory refinedW ->
                  Cont refinedD refinedW refinedBoundary ->
                    Cont refinedBoundary Q refinedRequest ->
                      PkgSig bundle P pkg ->
                        PkgSig bundle N pkg ->
                          SemanticNameCert
                              (fun row : BHist => hsame row refinedRequest ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row D ∨ hsame row W ∨ hsame row Q ∨
                                  hsame row restrictedD ∨ hsame row restrictedW ∨
                                    hsame row restrictedRequest ∨ hsame row refinedD ∨
                                      hsame row refinedW ∨ hsame row refinedBoundary ∨
                                        hsame row refinedRequest)
                              (fun row : BHist =>
                                UnaryHistory row ∧
                                  Cont restrictedD restrictedW restrictedBoundary ∧
                                    Cont restrictedBoundary Q restrictedRequest ∧
                                      Cont refinedD refinedW refinedBoundary ∧
                                        Cont refinedBoundary Q refinedRequest ∧
                                          PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                              hsame ∧
                            UnaryHistory restrictedRequest ∧ UnaryHistory refinedRequest := by
  -- BEDC touchpoint anchor: CauchyNetCompletionCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier restrictedDUnary restrictedWUnary restrictedBoundaryRoute restrictedRequestRoute
    refinedDUnary refinedWUnary refinedBoundaryRoute refinedRequestRoute provenancePkg localNamePkg
  obtain ⟨_unaryD, _unaryW, unaryQ, _unaryM, _unaryU, _unaryS, _unaryR, _unaryA,
    _unaryH, _unaryC, _unaryP, _unaryN, _carrierBoundaryRoute, _carrierMooreRoute,
      _carrierUniformRoute, _carrierSealRoute, _carrierPkgP, _carrierPkgN⟩ := carrier
  have restrictedBoundaryUnary : UnaryHistory restrictedBoundary :=
    unary_cont_closed restrictedDUnary restrictedWUnary restrictedBoundaryRoute
  have restrictedRequestUnary : UnaryHistory restrictedRequest :=
    unary_cont_closed restrictedBoundaryUnary unaryQ restrictedRequestRoute
  have refinedBoundaryUnary : UnaryHistory refinedBoundary :=
    unary_cont_closed refinedDUnary refinedWUnary refinedBoundaryRoute
  have refinedRequestUnary : UnaryHistory refinedRequest :=
    unary_cont_closed refinedBoundaryUnary unaryQ refinedRequestRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refinedRequest ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row Q ∨ hsame row restrictedD ∨
              hsame row restrictedW ∨ hsame row restrictedRequest ∨ hsame row refinedD ∨
                hsame row refinedW ∨ hsame row refinedBoundary ∨ hsame row refinedRequest)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont restrictedD restrictedW restrictedBoundary ∧
              Cont restrictedBoundary Q restrictedRequest ∧
                Cont refinedD refinedW refinedBoundary ∧
                  Cont refinedBoundary Q refinedRequest ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro refinedRequest ⟨hsame_refl refinedRequest, refinedRequestUnary⟩
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
        ⟨source.right, restrictedBoundaryRoute, restrictedRequestRoute, refinedBoundaryRoute,
          refinedRequestRoute, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, restrictedRequestUnary, refinedRequestUnary⟩

end BEDC.Derived.CauchyNetCompletionUp
