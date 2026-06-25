import BEDC.Derived.WassersteinUp.TasteGate

namespace BEDC.Derived.WassersteinUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem WassersteinMarginalExactnessScope [AskSetup] [PackageSetup]
    {M K mu nu Gamma A B C H R P N rowRead columnRead marginalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WassersteinTransportPlanCarrier M K mu nu Gamma A B C H R P N bundle pkg →
      Cont Gamma A rowRead →
        Cont Gamma B columnRead →
          Cont rowRead columnRead marginalRead →
            SemanticNameCert
                (fun row : BHist => hsame row marginalRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row mu ∨ hsame row nu ∨ hsame row Gamma ∨ hsame row A ∨
                    hsame row B ∨ hsame row rowRead ∨ hsame row columnRead ∨
                      hsame row marginalRead)
                (fun row : BHist =>
                  hsame row marginalRead ∧ Cont Gamma A rowRead ∧
                    Cont Gamma B columnRead ∧ Cont rowRead columnRead marginalRead ∧
                      PkgSig bundle P pkg)
                hsame ∧
              UnaryHistory rowRead ∧ UnaryHistory columnRead ∧
                UnaryHistory marginalRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory PkgSig
  intro carrier gammaRowRoute gammaColumnRoute marginalRoute
  obtain ⟨_mUnary, _kUnary, _muUnary, _nuUnary, gammaUnary, aUnary, bUnary, _cUnary,
    _hUnary, _rUnary, _pUnary, _nUnary, provenancePkg⟩ := carrier
  have rowUnary : UnaryHistory rowRead :=
    unary_cont_closed gammaUnary aUnary gammaRowRoute
  have columnUnary : UnaryHistory columnRead :=
    unary_cont_closed gammaUnary bUnary gammaColumnRoute
  have marginalUnary : UnaryHistory marginalRead :=
    unary_cont_closed rowUnary columnUnary marginalRoute
  have sourceAtMarginal :
      (fun row : BHist => hsame row marginalRead ∧ UnaryHistory row) marginalRead :=
    ⟨hsame_refl marginalRead, marginalUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row marginalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row mu ∨ hsame row nu ∨ hsame row Gamma ∨ hsame row A ∨
              hsame row B ∨ hsame row rowRead ∨ hsame row columnRead ∨
                hsame row marginalRead)
          (fun row : BHist =>
            hsame row marginalRead ∧ Cont Gamma A rowRead ∧ Cont Gamma B columnRead ∧
              Cont rowRead columnRead marginalRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro marginalRead sourceAtMarginal
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, gammaRowRoute, gammaColumnRoute, marginalRoute, provenancePkg⟩
  }
  exact ⟨cert, rowUnary, columnUnary, marginalUnary, provenancePkg⟩

end BEDC.Derived.WassersteinUp
