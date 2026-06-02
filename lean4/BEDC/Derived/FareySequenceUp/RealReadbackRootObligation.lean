import BEDC.Derived.FareySequenceUp.TasteGate

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceRealReadbackRootObligation [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N boundaryRead mediantRead denomRead
      toleranceRead sternRead rationalRead windowRead regseqRead approxRead sealedRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg ->
      Cont B A boundaryRead ->
        Cont boundaryRead M mediantRead ->
          Cont mediantRead L denomRead ->
            Cont denomRead T toleranceRead ->
              Cont toleranceRead S sternRead ->
                Cont sternRead Q rationalRead ->
                  Cont rationalRead W windowRead ->
                    Cont windowRead R regseqRead ->
                      Cont regseqRead G approxRead ->
                        Cont approxRead E sealedRead ->
                          Cont sealedRead N namedRead ->
                            PkgSig bundle P pkg ->
                              PkgSig bundle N pkg ->
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row sealedRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row boundaryRead ∨ hsame row mediantRead ∨
                                        hsame row denomRead ∨ hsame row toleranceRead ∨
                                          hsame row sternRead ∨ hsame row rationalRead ∨
                                            hsame row windowRead ∨ hsame row regseqRead ∨
                                              hsame row approxRead ∨
                                                hsame row sealedRead ∨
                                                  hsame row namedRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont windowRead R regseqRead ∧
                                        Cont regseqRead G approxRead ∧
                                          Cont approxRead E sealedRead ∧
                                            PkgSig bundle P pkg ∧
                                              PkgSig bundle N pkg)
                                    hsame ∧
                                  UnaryHistory boundaryRead ∧ UnaryHistory mediantRead ∧
                                    UnaryHistory denomRead ∧ UnaryHistory toleranceRead ∧
                                      UnaryHistory sternRead ∧ UnaryHistory rationalRead ∧
                                        UnaryHistory windowRead ∧ UnaryHistory regseqRead ∧
                                          UnaryHistory approxRead ∧
                                            UnaryHistory sealedRead ∧
                                              UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier boundaryRoute mediantRoute denomRoute toleranceRoute sternRoute
    rationalRoute windowRoute regseqRoute approxRoute sealedRoute namedRoute pkgP pkgN
  obtain ⟨bUnary, aUnary, mUnary, lUnary, tUnary, sUnary, _dUnary, qUnary, wUnary,
    rUnary, gUnary, eUnary, _hUnary, _cUnary, _pUnary, nUnary, _aEmpty, _sEmpty,
    _mEmpty, _gEmpty, _eEmpty, _carrierPkg⟩ := carrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed bUnary aUnary boundaryRoute
  have mediantUnary : UnaryHistory mediantRead :=
    unary_cont_closed boundaryUnary mUnary mediantRoute
  have denomUnary : UnaryHistory denomRead :=
    unary_cont_closed mediantUnary lUnary denomRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed denomUnary tUnary toleranceRoute
  have sternUnary : UnaryHistory sternRead :=
    unary_cont_closed toleranceUnary sUnary sternRoute
  have rationalUnary : UnaryHistory rationalRead :=
    unary_cont_closed sternUnary qUnary rationalRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed rationalUnary wUnary windowRoute
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed windowUnary rUnary regseqRoute
  have approxUnary : UnaryHistory approxRead :=
    unary_cont_closed regseqUnary gUnary approxRoute
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed approxUnary eUnary sealedRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealedUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row boundaryRead ∨ hsame row mediantRead ∨ hsame row denomRead ∨
              hsame row toleranceRead ∨ hsame row sternRead ∨ hsame row rationalRead ∨
                hsame row windowRead ∨ hsame row regseqRead ∨ hsame row approxRead ∨
                  hsame row sealedRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont windowRead R regseqRead ∧ Cont regseqRead G approxRead ∧
              Cont approxRead E sealedRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealedRead ⟨hsame_refl sealedRead, sealedUnary⟩
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
                          (Or.inl source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, regseqRoute, approxRoute, sealedRoute, pkgP, pkgN⟩
  }
  exact
    ⟨cert, boundaryUnary, mediantUnary, denomUnary, toleranceUnary, sternUnary,
      rationalUnary, windowUnary, regseqUnary, approxUnary, sealedUnary, namedUnary⟩

end BEDC.Derived.FareySequenceUp
