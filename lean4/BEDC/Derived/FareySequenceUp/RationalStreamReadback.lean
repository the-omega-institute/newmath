import BEDC.Derived.FareySequenceUp.TasteGate

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceRationalStreamReadback [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N rationalSource regularReadback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg ->
      Cont M L rationalSource ->
        Cont rationalSource W regularReadback ->
          PkgSig bundle P pkg ->
            PkgSig bundle N pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row regularReadback ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row L ∨
                      hsame row T ∨ hsame row Q ∨ hsame row W ∨ hsame row R ∨
                        hsame row regularReadback)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                  hsame ∧
                UnaryHistory rationalSource ∧ UnaryHistory regularReadback ∧
                  hsame regularReadback (append rationalSource W) := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier rationalRoute readbackRoute provenancePkg localPkg
  obtain ⟨_unaryB, _unaryA, unaryM, unaryL, _unaryT, _unaryS, _unaryD, _unaryQ,
    unaryW, _unaryR, _unaryG, _unaryE, _unaryH, _unaryC, _unaryP, _unaryN,
    _aEmpty, _sEmpty, _mEmpty, _gEmpty, _eEmpty, _carrierPkg⟩ := carrier
  have rationalUnary : UnaryHistory rationalSource :=
    unary_cont_closed unaryM unaryL rationalRoute
  have readbackUnary : UnaryHistory regularReadback :=
    unary_cont_closed rationalUnary unaryW readbackRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row regularReadback ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row L ∨ hsame row T ∨
              hsame row Q ∨ hsame row W ∨ hsame row R ∨ hsame row regularReadback)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro regularReadback ⟨hsame_refl regularReadback, readbackUnary⟩
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
      exact ⟨source.right, provenancePkg, localPkg⟩
  }
  have readbackSame : hsame regularReadback (append rationalSource W) := by
    cases readbackRoute
    rfl
  exact ⟨cert, rationalUnary, readbackUnary, readbackSame⟩

end BEDC.Derived.FareySequenceUp
