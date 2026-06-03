import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceRealSeparabilityForwardRoute [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M ratWindow dyadicTolerance streamSchedule
      regseqRead realSeal netRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg →
      Cont K0 K1 netRead →
        UnaryHistory ratWindow →
          UnaryHistory dyadicTolerance →
            UnaryHistory regseqRead →
              Cont ratWindow dyadicTolerance streamSchedule →
                Cont streamSchedule regseqRead realSeal →
                  PkgSig bundle realSeal pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row ratWindow ∨ hsame row dyadicTolerance ∨
                            hsame row streamSchedule ∨ hsame row regseqRead ∨
                              hsame row realSeal ∨ hsame row netRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle realSeal pkg)
                        hsame ∧
                      UnaryHistory netRead ∧ UnaryHistory streamSchedule ∧
                        UnaryHistory realSeal := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier netRoute ratUnary dyadicUnary regseqUnary scheduleRoute sealRoute realPkg
  obtain ⟨_xUnary, k0Unary, k1Unary, _n0Unary, _n1Unary, _d0Unary, _d1Unary,
    _rUnary, _hsUnary, _cUnary, _pUnary, _mUnary, provenancePkg⟩ := carrier
  have netUnary : UnaryHistory netRead :=
    unary_cont_closed k0Unary k1Unary netRoute
  have scheduleUnary : UnaryHistory streamSchedule :=
    unary_cont_closed ratUnary dyadicUnary scheduleRoute
  have realUnary : UnaryHistory realSeal :=
    unary_cont_closed scheduleUnary regseqUnary sealRoute
  have sourceReal :
      (fun row : BHist => hsame row realSeal ∧ UnaryHistory row) realSeal := by
    exact ⟨hsame_refl realSeal, realUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row ratWindow ∨ hsame row dyadicTolerance ∨
              hsame row streamSchedule ∨ hsame row regseqRead ∨
                hsame row realSeal ∨ hsame row netRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realSeal sourceReal
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
      exact Or.inl source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, realPkg⟩
  }
  exact ⟨cert, netUnary, scheduleUnary, realUnary⟩

end BEDC.Derived.HyperspaceUp
