import BEDC.Derived.CauchyCompletionMultiplicationUp.NameCertObligations
import BEDC.Derived.CauchyCompletionMultiplicationUp.TasteGate
import BEDC.Derived.CauchyCompletionMultiplicationUp.RealSealNonescape
import BEDC.FKernel.Cont.Assoc

namespace BEDC.Derived.CauchyCompletionMultiplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionMultiplication_flattening_route
    {M O I A S R D E MO MOI MOIA SR SRD publicFace flattened : BHist}
    (monadOuter : Cont M O MO)
    (idempotenceRoute : Cont MO I MOI)
    (associativityRoute : Cont MOI A MOIA)
    (streamReadback : Cont S R SR)
    (dyadicRoute : Cont SR D SRD)
    (realSealRoute : Cont SRD E publicFace)
    (flattenedRoute : Cont MOIA publicFace flattened) :
    Cont M (append O (append I (append A publicFace))) flattened ∧
      Cont S (append R (append D E)) publicFace := by
  -- BEDC touchpoint anchor: BHist Cont append
  constructor
  · cases monadOuter
    cases idempotenceRoute
    cases associativityRoute
    cases flattenedRoute
    exact
      (append_assoc (append (append M O) I) A publicFace).trans
        ((append_assoc (append M O) I (append A publicFace)).trans
          (append_assoc M O (append I (append A publicFace))))
  · cases streamReadback
    cases dyadicRoute
    cases realSealRoute
    exact
      (append_assoc (append S R) D E).trans
      (append_assoc S R (append D E))

theorem CauchyCompletionMultiplicationCarrier_outer_inner_replay [AskSetup] [PackageSetup]
    {M O I A S R D E H C P N flattenRead sealRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionMultiplicationCarrier M O I A S R D E H C P N bundle pkg ->
      Cont M O flattenRead ->
        Cont S R sealRead ->
          Cont flattenRead sealRead replayRead ->
            PkgSig bundle replayRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row flattenRead ∨ hsame row sealRead ∨ hsame row replayRead)
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle replayRead pkg)
                  hsame ∧ UnaryHistory replayRead ∧
                Cont flattenRead sealRead replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro carrier flattenRoute sealRoute replayRoute replayPkg
  obtain ⟨mUnary, oUnary, _iUnary, _aUnary, sUnary, rUnary, _dUnary, _eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _hM, _cP, _provenancePkg, _namePkg⟩ := carrier
  have flattenUnary : UnaryHistory flattenRead :=
    unary_cont_closed mUnary oUnary flattenRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed sUnary rUnary sealRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed flattenUnary sealUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row flattenRead ∨ hsame row sealRead ∨ hsame row replayRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle replayRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, replayPkg⟩
  }
  exact ⟨cert, replayUnary, replayRoute⟩

end BEDC.Derived.CauchyCompletionMultiplicationUp
