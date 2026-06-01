import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperspaceVietorisUnionStability [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M X' K0' K1' N0' N1' D0' D1' R' Hs' C' P'
      M' unionHit unionMiss unionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg →
      HyperspaceCarrier X' K0' K1' N0' N1' D0' D1' R' Hs' C' P' M' bundle pkg →
        Cont K0 K0' unionHit →
          Cont K1 K1' unionMiss →
            Cont unionHit unionMiss unionRead →
              PkgSig bundle P pkg →
                PkgSig bundle M pkg →
                  UnaryHistory unionHit ∧ UnaryHistory unionMiss ∧
                    UnaryHistory unionRead ∧ hsame unionRead (append unionHit unionMiss) ∧
                      SemanticNameCert
                        (fun row : BHist => hsame row unionRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row K0 ∨ hsame row K0' ∨ hsame row K1 ∨
                            hsame row K1' ∨ hsame row unionHit ∨
                              hsame row unionMiss ∨ hsame row unionRead)
                        (fun row : BHist =>
                          hsame row unionRead ∧ Cont unionHit unionMiss unionRead ∧
                            PkgSig bundle P pkg ∧ PkgSig bundle M pkg)
                        hsame := by
  -- BEDC touchpoint anchor: BHist HyperspaceCarrier Cont ProbeBundle PkgSig SemanticNameCert
  intro carrier carrier' hitRoute missRoute readRoute provenancePkg missPkg
  obtain ⟨_xUnary, k0Unary, k1Unary, _n0Unary, _n1Unary, _d0Unary, _d1Unary,
    _rUnary, _hsUnary, _cUnary, _pUnary, _mUnary, _carrierPkg⟩ := carrier
  obtain ⟨_x'Unary, k0'Unary, k1'Unary, _n0'Unary, _n1'Unary, _d0'Unary,
    _d1'Unary, _r'Unary, _hs'Unary, _c'Unary, _p'Unary, _m'Unary,
    _carrierPkg'⟩ := carrier'
  have unionHitUnary : UnaryHistory unionHit :=
    unary_cont_closed k0Unary k0'Unary hitRoute
  have unionMissUnary : UnaryHistory unionMiss :=
    unary_cont_closed k1Unary k1'Unary missRoute
  have unionReadUnary : UnaryHistory unionRead :=
    unary_cont_closed unionHitUnary unionMissUnary readRoute
  have unionExact : hsame unionRead (append unionHit unionMiss) := readRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row unionRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row K0 ∨ hsame row K0' ∨ hsame row K1 ∨ hsame row K1' ∨
            hsame row unionHit ∨ hsame row unionMiss ∨ hsame row unionRead)
        (fun row : BHist =>
          hsame row unionRead ∧ Cont unionHit unionMiss unionRead ∧
            PkgSig bundle P pkg ∧ PkgSig bundle M pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro unionRead ⟨hsame_refl unionRead, unionReadUnary⟩
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
      exact ⟨source.left, readRoute, provenancePkg, missPkg⟩
  }
  exact ⟨unionHitUnary, unionMissUnary, unionReadUnary, unionExact, cert⟩

end BEDC.Derived.HyperspaceUp
