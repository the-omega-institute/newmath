import BEDC.Derived.CauchyNetCompletionUp.MooreSmithHandoff

namespace BEDC.Derived.CauchyNetCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyNetCompletionDirectedWindowCofinalRestriction [AskSetup] [PackageSetup]
    {D W Q M U S R A H C P N restrictedD restrictedW restrictedBoundary
      restrictedRequest : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyNetCompletionCarrier D W Q M U S R A H C P N bundle pkg ->
      UnaryHistory restrictedD ->
        UnaryHistory restrictedW ->
          Cont restrictedD restrictedW restrictedBoundary ->
            Cont restrictedBoundary Q restrictedRequest ->
              PkgSig bundle P pkg ->
                PkgSig bundle N pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row restrictedRequest ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row restrictedD ∨ hsame row restrictedW ∨ hsame row Q ∨
                          hsame row M ∨ hsame row U ∨ hsame row S ∨ hsame row R ∨
                            hsame row A ∨ hsame row restrictedBoundary ∨
                              hsame row restrictedRequest)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont restrictedD restrictedW restrictedBoundary ∧
                          Cont restrictedBoundary Q restrictedRequest ∧
                            PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                      hsame ∧
                    UnaryHistory restrictedBoundary ∧ UnaryHistory restrictedRequest := by
  -- BEDC touchpoint anchor: CauchyNetCompletionCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier restrictedDUnary restrictedWUnary restrictedBoundaryRoute restrictedRequestRoute
    provenancePkg localNamePkg
  obtain ⟨_unaryD, _unaryW, unaryQ, _unaryM, _unaryU, _unaryS, _unaryR, _unaryA,
    _unaryH, _unaryC, _unaryP, _unaryN, _carrierBoundaryRoute, _carrierMooreRoute,
      _carrierUniformRoute, _carrierSealRoute, _carrierPkgP, _carrierPkgN⟩ := carrier
  have restrictedBoundaryUnary : UnaryHistory restrictedBoundary :=
    unary_cont_closed restrictedDUnary restrictedWUnary restrictedBoundaryRoute
  have restrictedRequestUnary : UnaryHistory restrictedRequest :=
    unary_cont_closed restrictedBoundaryUnary unaryQ restrictedRequestRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row restrictedRequest ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row restrictedD ∨ hsame row restrictedW ∨ hsame row Q ∨ hsame row M ∨
              hsame row U ∨ hsame row S ∨ hsame row R ∨ hsame row A ∨
                hsame row restrictedBoundary ∨ hsame row restrictedRequest)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont restrictedD restrictedW restrictedBoundary ∧
              Cont restrictedBoundary Q restrictedRequest ∧ PkgSig bundle P pkg ∧
                PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro restrictedRequest ⟨hsame_refl restrictedRequest, restrictedRequestUnary⟩
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
        ⟨source.right, restrictedBoundaryRoute, restrictedRequestRoute, provenancePkg,
          localNamePkg⟩
  }
  exact ⟨cert, restrictedBoundaryUnary, restrictedRequestUnary⟩

end BEDC.Derived.CauchyNetCompletionUp
