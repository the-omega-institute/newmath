import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceHausdorffClassifierTransport [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M distanceRead publicRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg →
      Cont D0 D1 distanceRead →
        Cont distanceRead R publicRead →
          Cont Hs publicRead replayRead →
            PkgSig bundle P pkg →
              PkgSig bundle M pkg →
                UnaryHistory distanceRead ∧ UnaryHistory publicRead ∧
                  UnaryHistory replayRead ∧ hsame distanceRead (append D0 D1) ∧
                    SemanticNameCert
                      (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row X ∨ hsame row D0 ∨ hsame row D1 ∨
                          hsame row R ∨ hsame row Hs ∨ hsame row C ∨
                            hsame row P ∨ hsame row M ∨ hsame row distanceRead ∨
                              hsame row publicRead ∨ hsame row replayRead)
                      (fun row : BHist =>
                        hsame row replayRead ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle M pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro carrier distanceRoute publicRoute replayRoute provenancePkg namePkg
  obtain ⟨_xUnary, _k0Unary, _k1Unary, _n0Unary, _n1Unary, d0Unary, d1Unary,
    rUnary, hsUnary, _cUnary, _pUnary, _mUnary, _carrierPkg⟩ := carrier
  have distanceUnary : UnaryHistory distanceRead :=
    unary_cont_closed d0Unary d1Unary distanceRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed distanceUnary rUnary publicRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed hsUnary publicUnary replayRoute
  have distanceExact : hsame distanceRead (append D0 D1) := distanceRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row X ∨ hsame row D0 ∨ hsame row D1 ∨ hsame row R ∨
            hsame row Hs ∨ hsame row C ∨ hsame row P ∨ hsame row M ∨
              hsame row distanceRead ∨ hsame row publicRead ∨ hsame row replayRead)
        (fun row : BHist =>
          hsame row replayRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle M pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg, namePkg⟩
  }
  exact ⟨distanceUnary, publicUnary, replayUnary, distanceExact, cert⟩

end BEDC.Derived.HyperspaceUp
