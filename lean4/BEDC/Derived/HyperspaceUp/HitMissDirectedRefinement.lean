import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem Hyperspace_hit_miss_directed_refinement [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M X' K0' K1' N0' N1' D0' D1' R' Hs' C' P'
      M' refinedHit refinedMiss refinedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg →
      HyperspaceCarrier X' K0' K1' N0' N1' D0' D1' R' Hs' C' P' M' bundle pkg →
        hsame X' X →
          hsame K0' K0 →
            hsame K1' K1 →
              Cont D0' D0 refinedHit →
                Cont D1' D1 refinedMiss →
                  Cont refinedHit refinedMiss refinedRead →
                    PkgSig bundle refinedRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row refinedRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨
                              hsame row D0 ∨ hsame row D1 ∨ hsame row refinedHit ∨
                                hsame row refinedMiss ∨ hsame row refinedRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont D0' D0 refinedHit ∧
                              Cont D1' D1 refinedMiss ∧
                                Cont refinedHit refinedMiss refinedRead ∧
                                  PkgSig bundle refinedRead pkg)
                          hsame ∧
                        UnaryHistory refinedHit ∧ UnaryHistory refinedMiss ∧
                          UnaryHistory refinedRead := by
  -- BEDC touchpoint anchor: HyperspaceCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier carrier' _sameX _sameK0 _sameK1 hitRoute missRoute readRoute readPkg
  obtain ⟨_xUnary, _k0Unary, _k1Unary, _n0Unary, _n1Unary, d0Unary, d1Unary,
    _rUnary, _hsUnary, _cUnary, _pUnary, _mUnary, _provenancePkg⟩ := carrier
  obtain ⟨_x'Unary, _k0'Unary, _k1'Unary, _n0'Unary, _n1'Unary, d0'Unary,
    d1'Unary, _r'Unary, _hs'Unary, _c'Unary, _p'Unary, _m'Unary,
    _provenancePkg'⟩ := carrier'
  have refinedHitUnary : UnaryHistory refinedHit :=
    unary_cont_closed d0'Unary d0Unary hitRoute
  have refinedMissUnary : UnaryHistory refinedMiss :=
    unary_cont_closed d1'Unary d1Unary missRoute
  have refinedReadUnary : UnaryHistory refinedRead :=
    unary_cont_closed refinedHitUnary refinedMissUnary readRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refinedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row D0 ∨
              hsame row D1 ∨ hsame row refinedHit ∨ hsame row refinedMiss ∨
                hsame row refinedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D0' D0 refinedHit ∧ Cont D1' D1 refinedMiss ∧
              Cont refinedHit refinedMiss refinedRead ∧ PkgSig bundle refinedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro refinedRead ⟨hsame_refl refinedRead, refinedReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, hitRoute, missRoute, readRoute, readPkg⟩
  }
  exact ⟨cert, refinedHitUnary, refinedMissUnary, refinedReadUnary⟩

end BEDC.Derived.HyperspaceUp
