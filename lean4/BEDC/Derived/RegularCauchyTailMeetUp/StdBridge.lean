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

theorem RegularCauchyTailMeetUp_StdBridge [AskSetup] [PackageSetup]
    {r0 r1 w0 w1 m0 m1 tau q h c l n realSeal diagonalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailMeetPacket r0 r1 w0 w1 m0 m1 tau q h c l n bundle pkg ->
      Cont l n realSeal ->
        Cont tau realSeal diagonalRead ->
          PkgSig bundle realSeal pkg ->
            PkgSig bundle diagonalRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row diagonalRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row r0 ∨ hsame row r1 ∨ hsame row w0 ∨ hsame row w1 ∨
                      hsame row tau ∨ hsame row q ∨ hsame row l ∨
                        hsame row realSeal ∨ hsame row diagonalRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont m0 m1 tau ∧ Cont tau q l ∧
                      Cont l n realSeal ∧ Cont tau realSeal diagonalRead ∧
                        PkgSig bundle l pkg ∧ PkgSig bundle realSeal pkg ∧
                          PkgSig bundle diagonalRead pkg)
                  hsame ∧
                UnaryHistory tau ∧ UnaryHistory l ∧ UnaryHistory realSeal ∧
                  UnaryHistory diagonalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet sealRoute diagonalRoute realSealPkg diagonalPkg
  obtain ⟨_r0Unary, _r1Unary, _w0Unary, _w1Unary, m0Unary, m1Unary, tauUnary,
    qUnary, _hUnary, _cUnary, lUnary, nUnary, _r0w0Row, _r1w1Row, m0m1Row,
    tauqRow, thresholdPkg⟩ := packet
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed lUnary nUnary sealRoute
  have diagonalUnary : UnaryHistory diagonalRead :=
    unary_cont_closed tauUnary realSealUnary diagonalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row diagonalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row r0 ∨ hsame row r1 ∨ hsame row w0 ∨ hsame row w1 ∨
              hsame row tau ∨ hsame row q ∨ hsame row l ∨ hsame row realSeal ∨
                hsame row diagonalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont m0 m1 tau ∧ Cont tau q l ∧ Cont l n realSeal ∧
              Cont tau realSeal diagonalRead ∧ PkgSig bundle l pkg ∧
                PkgSig bundle realSeal pkg ∧ PkgSig bundle diagonalRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro diagonalRead ⟨hsame_refl diagonalRead, diagonalUnary⟩
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
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, m0m1Row, tauqRow, sealRoute, diagonalRoute, thresholdPkg,
          realSealPkg, diagonalPkg⟩
  }
  exact ⟨cert, tauUnary, lUnary, realSealUnary, diagonalUnary⟩

end BEDC.Derived.RegularCauchyTailMeetUp
