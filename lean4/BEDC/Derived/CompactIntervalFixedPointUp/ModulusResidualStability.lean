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

theorem CompactIntervalFixedPoint_modulus_residual_stability [AskSetup] [PackageSetup]
    {J G R B W Q E H C P N residualRead refinedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactIntervalFixedPointCarrier J G R B W Q E H C P N bundle pkg →
      Cont G R residualRead →
        Cont residualRead C refinedRead →
          PkgSig bundle refinedRead pkg →
            SemanticNameCert
              (fun row : BHist =>
                hsame row refinedRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
              (fun row : BHist =>
                hsame row J ∨ hsame row G ∨ hsame row R ∨ hsame row residualRead ∨
                  hsame row refinedRead ∨ hsame row P)
              (fun row : BHist =>
                hsame row refinedRead ∧ Cont G R residualRead ∧
                  Cont residualRead C refinedRead ∧ PkgSig bundle P pkg)
              hsame ∧ UnaryHistory residualRead ∧ UnaryHistory refinedRead := by
  -- BEDC touchpoint anchor: CompactIntervalFixedPointCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier residualRoute refinedRoute refinedPkg
  obtain ⟨_jUnary, gUnary, rUnary, _bUnary, _wUnary, _qUnary, _eUnary, _hUnary,
    cUnary, _pUnary, _nUnary, provenancePkg, _namePkg, _packetWitness⟩ := carrier
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed gUnary rUnary residualRoute
  have refinedUnary : UnaryHistory refinedRead :=
    unary_cont_closed residualUnary cUnary refinedRoute
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row refinedRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
        (fun row : BHist =>
          hsame row J ∨ hsame row G ∨ hsame row R ∨ hsame row residualRead ∨
            hsame row refinedRead ∨ hsame row P)
        (fun row : BHist =>
          hsame row refinedRead ∧ Cont G R residualRead ∧
            Cont residualRead C refinedRead ∧ PkgSig bundle P pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro refinedRead
        ⟨hsame_refl refinedRead, refinedUnary, refinedPkg⟩
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
        intro _row _other sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sourceRow.left))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, residualRoute, refinedRoute, provenancePkg⟩
  }
  exact ⟨cert, residualUnary, refinedUnary⟩

end BEDC.Derived.CompactIntervalFixedPointUp.ModulusResidualStability
