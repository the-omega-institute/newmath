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

theorem FareySequenceCarrier_real_rational_approximation_unblock [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N adjacentRead mediantRead toleranceRead densityRead
      rationalRead streamRead regularRead approximationRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg ->
      Cont B A adjacentRead ->
        Cont adjacentRead M mediantRead ->
          Cont mediantRead T toleranceRead ->
            Cont toleranceRead D densityRead ->
              Cont densityRead Q rationalRead ->
                Cont rationalRead W streamRead ->
                  Cont streamRead R regularRead ->
                    Cont regularRead G approximationRead ->
                      Cont approximationRead E sealRead ->
                        Cont sealRead N namedRead ->
                          PkgSig bundle P pkg ->
                            PkgSig bundle N pkg ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row B ∨ hsame row A ∨ hsame row M ∨
                                      hsame row T ∨ hsame row D ∨ hsame row Q ∨
                                        hsame row W ∨ hsame row R ∨ hsame row G ∨
                                          hsame row E ∨ hsame row N ∨ hsame row namedRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont approximationRead E sealRead ∧
                                      Cont sealRead N namedRead ∧ PkgSig bundle P pkg ∧
                                        PkgSig bundle N pkg)
                                  hsame ∧
                                UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier adjacentRoute mediantRoute toleranceRoute densityRoute rationalRoute
    streamRoute regularRoute approximationRoute sealRoute namedRoute pkgP pkgN
  obtain ⟨bUnary, aUnary, mUnary, _lUnary, tUnary, _sUnary, dUnary, qUnary, wUnary,
    rUnary, gUnary, eUnary, _hUnary, _cUnary, _pUnary, nUnary, _aEmpty, _sEmpty,
    _mEmpty, _gEmpty, _eEmpty, _carrierPkg⟩ := carrier
  have adjacentUnary : UnaryHistory adjacentRead :=
    unary_cont_closed bUnary aUnary adjacentRoute
  have mediantUnary : UnaryHistory mediantRead :=
    unary_cont_closed adjacentUnary mUnary mediantRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed mediantUnary tUnary toleranceRoute
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed toleranceUnary dUnary densityRoute
  have rationalUnary : UnaryHistory rationalRead :=
    unary_cont_closed densityUnary qUnary rationalRoute
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed rationalUnary wUnary streamRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed streamUnary rUnary regularRoute
  have approximationUnary : UnaryHistory approximationRead :=
    unary_cont_closed regularUnary gUnary approximationRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed approximationUnary eUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row T ∨ hsame row D ∨
              hsame row Q ∨ hsame row W ∨ hsame row R ∨ hsame row G ∨ hsame row E ∨
                hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont approximationRead E sealRead ∧
              Cont sealRead N namedRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
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
      exact ⟨source.right, sealRoute, namedRoute, pkgP, pkgN⟩
  }
  exact ⟨cert, namedUnary⟩

end BEDC.Derived.FareySequenceUp
