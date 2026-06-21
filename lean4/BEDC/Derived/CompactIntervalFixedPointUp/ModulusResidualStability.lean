import BEDC.Derived.CompactIntervalFixedPointUp.PublicSeal

namespace BEDC.Derived.CompactIntervalFixedPointUp.ModulusResidualStability

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactIntervalFixedPointModulusResidualStability [AskSetup] [PackageSetup]
    {J G R B W Q E H C P N residualRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactIntervalFixedPointCarrier J G R B W Q E H C P N bundle pkg →
      Cont G R residualRead →
        Cont residualRead J replayRead →
          PkgSig bundle replayRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row J ∨ hsame row G ∨ hsame row R ∨ hsame row B ∨
                    hsame row H ∨ hsame row C ∨ hsame row replayRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont G R residualRead ∧
                    Cont residualRead J replayRead ∧ PkgSig bundle replayRead pkg)
                hsame ∧ UnaryHistory residualRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory PkgSig
  intro carrier residualRoute replayRoute replayPkg
  obtain ⟨jUnary, gUnary, rUnary, _bUnary, _wUnary, _qUnary, _eUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _provenancePkg, _namePkg, _packetWitness⟩ := carrier
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed gUnary rUnary residualRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed residualUnary jUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row J ∨ hsame row G ∨ hsame row R ∨ hsame row B ∨ hsame row H ∨
              hsame row C ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont G R residualRead ∧ Cont residualRead J replayRead ∧
              PkgSig bundle replayRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead
        ⟨hsame_refl replayRead, replayUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, residualRoute, replayRoute, replayPkg⟩
  }
  exact ⟨cert, residualUnary, replayUnary⟩

end BEDC.Derived.CompactIntervalFixedPointUp.ModulusResidualStability
