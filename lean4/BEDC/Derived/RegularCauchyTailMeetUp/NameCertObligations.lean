import BEDC.Derived.RegularCauchyTailMeetUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RegularCauchyTailMeetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyTailMeetPacket_namecert_obligations [AskSetup] [PackageSetup]
    {r0 r1 w0 w1 m0 m1 tau q h c l n realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailMeetPacket r0 r1 w0 w1 m0 m1 tau q h c l n bundle pkg ->
      Cont l n realSeal ->
        PkgSig bundle realSeal pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row r0 ∨ hsame row r1 ∨ hsame row w0 ∨ hsame row w1 ∨
                  hsame row m0 ∨ hsame row m1 ∨ hsame row tau ∨ hsame row q ∨
                    hsame row l ∨ hsame row n ∨ hsame row realSeal)
              (fun row : BHist => PkgSig bundle realSeal pkg ∧ hsame row realSeal)
              hsame ∧
            UnaryHistory realSeal ∧ Cont l n realSeal ∧ PkgSig bundle l pkg ∧
              PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet sealRoute realSealPkg
  obtain ⟨_r0Unary, _r1Unary, _w0Unary, _w1Unary, _m0Unary, _m1Unary,
    _tauUnary, _qUnary, _hUnary, _cUnary, lUnary, nUnary, _r0w0Row, _r1w1Row,
    _m0m1Row, _tauqRow, pkgRow⟩ := packet
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed lUnary nUnary sealRoute
  have sourceSeal :
      (fun row : BHist => hsame row realSeal ∧ UnaryHistory row) realSeal := by
    exact ⟨hsame_refl realSeal, realSealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row r0 ∨ hsame row r1 ∨ hsame row w0 ∨ hsame row w1 ∨
              hsame row m0 ∨ hsame row m1 ∨ hsame row tau ∨ hsame row q ∨
                hsame row l ∨ hsame row n ∨ hsame row realSeal)
          (fun row : BHist => PkgSig bundle realSeal pkg ∧ hsame row realSeal)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realSeal sourceSeal
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨realSealPkg, source.left⟩
  }
  exact ⟨cert, realSealUnary, sealRoute, pkgRow, realSealPkg⟩

end BEDC.Derived.RegularCauchyTailMeetUp
