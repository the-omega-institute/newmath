import BEDC.Derived.FareySequenceUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceRationalCoverage [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N dyadicRead streamRead regseqRead approxRead
      sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg ->
      Cont Q T dyadicRead ->
        Cont Q W streamRead ->
          Cont streamRead R regseqRead ->
            Cont regseqRead G approxRead ->
              Cont approxRead E sealRead ->
                Cont sealRead N namedRead ->
                  PkgSig bundle P pkg ->
                    PkgSig bundle N pkg ->
                      SemanticNameCert
                            (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row Q ∨ hsame row T ∨ hsame row W ∨ hsame row R ∨
                                hsame row G ∨ hsame row E ∨ hsame row dyadicRead ∨
                                  hsame row streamRead ∨ hsame row regseqRead ∨
                                    hsame row approxRead ∨ hsame row sealRead ∨
                                      hsame row namedRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont Q T dyadicRead ∧
                                Cont Q W streamRead ∧ Cont streamRead R regseqRead ∧
                                  Cont regseqRead G approxRead ∧
                                    Cont approxRead E sealRead ∧ PkgSig bundle P pkg ∧
                                      PkgSig bundle N pkg)
                            hsame ∧
                          UnaryHistory dyadicRead ∧ UnaryHistory streamRead ∧
                            UnaryHistory regseqRead ∧ UnaryHistory approxRead ∧
                              UnaryHistory sealRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier dyadicRoute streamRoute regseqRoute approxRoute sealRoute namedRoute pkgP
    pkgN
  obtain ⟨_bUnary, _aUnary, _mUnary, _lUnary, tUnary, _sUnary, _dUnary, qUnary,
    wUnary, rUnary, gUnary, eUnary, _hUnary, _cUnary, _pUnary, nUnary, _aEmpty,
    _sEmpty, _mEmpty, _gEmpty, _eEmpty, _carrierPkg⟩ := carrier
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed qUnary tUnary dyadicRoute
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed qUnary wUnary streamRoute
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed streamUnary rUnary regseqRoute
  have approxUnary : UnaryHistory approxRead :=
    unary_cont_closed regseqUnary gUnary approxRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed approxUnary eUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row T ∨ hsame row W ∨ hsame row R ∨ hsame row G ∨
              hsame row E ∨ hsame row dyadicRead ∨ hsame row streamRead ∨
                hsame row regseqRead ∨ hsame row approxRead ∨ hsame row sealRead ∨
                  hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q T dyadicRead ∧ Cont Q W streamRead ∧
              Cont streamRead R regseqRead ∧ Cont regseqRead G approxRead ∧
                Cont approxRead E sealRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
                          (Or.inr
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, dyadicRoute, streamRoute, regseqRoute, approxRoute, sealRoute, pkgP,
          pkgN⟩
  }
  exact
    ⟨cert, dyadicUnary, streamUnary, regseqUnary, approxUnary, sealUnary, namedUnary⟩

end BEDC.Derived.FareySequenceUp
