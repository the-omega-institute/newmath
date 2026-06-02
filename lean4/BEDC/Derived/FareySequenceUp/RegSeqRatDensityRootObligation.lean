import BEDC.Derived.FareySequenceUp.TasteGate

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceRegSeqRatDensityRootObligation [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N boundaryRead mediantRead denomRead
      toleranceRead densityRead rationalRead windowRead regseqRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg →
      Cont B A boundaryRead →
        Cont boundaryRead M mediantRead →
          Cont mediantRead L denomRead →
            Cont denomRead T toleranceRead →
              Cont toleranceRead D densityRead →
                Cont densityRead Q rationalRead →
                  Cont rationalRead W windowRead →
                    Cont windowRead R regseqRead →
                      Cont regseqRead N namedRead →
                        PkgSig bundle P pkg →
                          PkgSig bundle N pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row regseqRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row boundaryRead ∨ hsame row mediantRead ∨
                                    hsame row denomRead ∨ hsame row toleranceRead ∨
                                      hsame row densityRead ∨ hsame row rationalRead ∨
                                        hsame row windowRead ∨ hsame row regseqRead ∨
                                          hsame row namedRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont windowRead R regseqRead ∧
                                    PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory boundaryRead ∧ UnaryHistory mediantRead ∧
                                UnaryHistory denomRead ∧ UnaryHistory toleranceRead ∧
                                  UnaryHistory densityRead ∧ UnaryHistory rationalRead ∧
                                    UnaryHistory windowRead ∧ UnaryHistory regseqRead ∧
                                      UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier boundaryRoute mediantRoute denomRoute toleranceRoute densityRoute rationalRoute
    windowRoute regseqRoute namedRoute pkgP pkgN
  obtain ⟨bUnary, aUnary, mUnary, lUnary, tUnary, _sUnary, dUnary, qUnary, wUnary,
    rUnary, _gUnary, _eUnary, _hUnary, _cUnary, _pUnary, nUnary, _aEmpty, _sEmpty,
    _mEmpty, _gEmpty, _eEmpty, _carrierPkg⟩ := carrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed bUnary aUnary boundaryRoute
  have mediantUnary : UnaryHistory mediantRead :=
    unary_cont_closed boundaryUnary mUnary mediantRoute
  have denomUnary : UnaryHistory denomRead :=
    unary_cont_closed mediantUnary lUnary denomRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed denomUnary tUnary toleranceRoute
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed toleranceUnary dUnary densityRoute
  have rationalUnary : UnaryHistory rationalRead :=
    unary_cont_closed densityUnary qUnary rationalRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed rationalUnary wUnary windowRoute
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed windowUnary rUnary regseqRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed regseqUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row regseqRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row boundaryRead ∨ hsame row mediantRead ∨ hsame row denomRead ∨
              hsame row toleranceRead ∨ hsame row densityRead ∨ hsame row rationalRead ∨
                hsame row windowRead ∨ hsame row regseqRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont windowRead R regseqRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro regseqRead ⟨hsame_refl regseqRead, regseqUnary⟩
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
                      (Or.inl source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, regseqRoute, pkgP, pkgN⟩
  }
  exact
    ⟨cert, boundaryUnary, mediantUnary, denomUnary, toleranceUnary, densityUnary,
      rationalUnary, windowUnary, regseqUnary, namedUnary⟩

end BEDC.Derived.FareySequenceUp
