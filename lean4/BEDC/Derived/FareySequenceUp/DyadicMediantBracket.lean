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

theorem FareySequenceCarrier_dyadic_mediant_bracket [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N adjacentRead mediantRead denominatorRead
      toleranceRead streamRead regularRead approximationRead sealRead bracketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg ->
      Cont B A adjacentRead ->
        Cont adjacentRead M mediantRead ->
          Cont mediantRead L denominatorRead ->
            Cont denominatorRead T toleranceRead ->
              Cont Q W streamRead ->
                Cont streamRead R regularRead ->
                  Cont regularRead G approximationRead ->
                    Cont approximationRead E sealRead ->
                      Cont toleranceRead streamRead bracketRead ->
                        PkgSig bundle P pkg ->
                          PkgSig bundle N pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row bracketRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row B ∨ hsame row A ∨ hsame row M ∨
                                    hsame row L ∨ hsame row T ∨ hsame row Q ∨
                                      hsame row W ∨ hsame row R ∨ hsame row G ∨
                                        hsame row E ∨ hsame row bracketRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont toleranceRead streamRead bracketRead ∧
                                    PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory bracketRead := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier adjacentRoute mediantRoute denominatorRoute toleranceRoute streamRoute
    regularRoute approximationRoute sealRoute bracketRoute pkgP pkgN
  obtain ⟨bUnary, aUnary, mUnary, lUnary, tUnary, _sUnary, _dUnary, qUnary, wUnary,
    rUnary, gUnary, eUnary, _hUnary, _cUnary, _pUnary, _nUnary, _aEmpty, _sEmpty,
    _mEmpty, _gEmpty, _eEmpty, _carrierPkg⟩ := carrier
  have adjacentUnary : UnaryHistory adjacentRead :=
    unary_cont_closed bUnary aUnary adjacentRoute
  have mediantUnary : UnaryHistory mediantRead :=
    unary_cont_closed adjacentUnary mUnary mediantRoute
  have denominatorUnary : UnaryHistory denominatorRead :=
    unary_cont_closed mediantUnary lUnary denominatorRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed denominatorUnary tUnary toleranceRoute
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed qUnary wUnary streamRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed streamUnary rUnary regularRoute
  have approximationUnary : UnaryHistory approximationRead :=
    unary_cont_closed regularUnary gUnary approximationRoute
  have _sealUnary : UnaryHistory sealRead :=
    unary_cont_closed approximationUnary eUnary sealRoute
  have bracketUnary : UnaryHistory bracketRead :=
    unary_cont_closed toleranceUnary streamUnary bracketRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bracketRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row L ∨ hsame row T ∨
              hsame row Q ∨ hsame row W ∨ hsame row R ∨ hsame row G ∨ hsame row E ∨
                hsame row bracketRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont toleranceRead streamRead bracketRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bracketRead ⟨hsame_refl bracketRead, bracketUnary⟩
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
      exact ⟨source.right, bracketRoute, pkgP, pkgN⟩
  }
  exact ⟨cert, bracketUnary⟩

end BEDC.Derived.FareySequenceUp
