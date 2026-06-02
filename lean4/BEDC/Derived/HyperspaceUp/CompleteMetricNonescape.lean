import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem Hyperspace_complete_metric_nonescape [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M subsetRead distanceRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg →
      Cont K0 K1 subsetRead →
        Cont D0 D1 distanceRead →
          Cont subsetRead distanceRead completionRead →
            PkgSig bundle completionRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row D0 ∨
                      hsame row D1 ∨ hsame row subsetRead ∨ hsame row distanceRead ∨
                        hsame row completionRead)
                  (fun row : BHist =>
                    hsame row completionRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle completionRead pkg)
                  hsame ∧
                UnaryHistory subsetRead ∧ UnaryHistory distanceRead ∧
                  UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: HyperspaceCarrier BHist ProbeBundle Pkg Cont SemanticNameCert
  intro carrier subsetRoute distanceRoute completionRoute completionPkg
  obtain ⟨_xUnary, k0Unary, k1Unary, _n0Unary, _n1Unary, d0Unary, d1Unary,
    _rUnary, _hsUnary, _cUnary, _pUnary, _mUnary, provenancePkg⟩ := carrier
  have subsetUnary : UnaryHistory subsetRead :=
    unary_cont_closed k0Unary k1Unary subsetRoute
  have distanceUnary : UnaryHistory distanceRead :=
    unary_cont_closed d0Unary d1Unary distanceRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed subsetUnary distanceUnary completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row D0 ∨
              hsame row D1 ∨ hsame row subsetRead ∨ hsame row distanceRead ∨
                hsame row completionRead)
          (fun row : BHist =>
            hsame row completionRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead ⟨hsame_refl completionRead, completionUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg, completionPkg⟩
  }
  exact ⟨cert, subsetUnary, distanceUnary, completionUnary⟩

end BEDC.Derived.HyperspaceUp
