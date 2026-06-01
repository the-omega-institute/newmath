import BEDC.Derived.FareySequenceUp.TasteGate

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceFiniteDensityRootPackage [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N boundaryRead levelRead toleranceRead sternRead
      densityRead rationalRead windowRead regseqRead approxRead sealedRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg →
      Cont B A boundaryRead →
        Cont boundaryRead M levelRead →
          Cont levelRead L toleranceRead →
            Cont toleranceRead S sternRead →
              Cont sternRead D densityRead →
                Cont densityRead Q rationalRead →
                  Cont rationalRead W windowRead →
                    Cont windowRead R regseqRead →
                      Cont regseqRead G approxRead →
                        Cont approxRead E sealedRead →
                          Cont sealedRead H namedRead →
                            PkgSig bundle P pkg →
                              PkgSig bundle N pkg →
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row sealedRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row boundaryRead ∨ hsame row levelRead ∨
                                        hsame row toleranceRead ∨ hsame row sternRead ∨
                                          hsame row densityRead ∨ hsame row rationalRead ∨
                                            hsame row windowRead ∨ hsame row regseqRead ∨
                                              hsame row approxRead ∨ hsame row sealedRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont windowRead R regseqRead ∧
                                        Cont regseqRead G approxRead ∧
                                          Cont approxRead E sealedRead ∧
                                            PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                    hsame ∧
                                  UnaryHistory boundaryRead ∧
                                    UnaryHistory levelRead ∧
                                      UnaryHistory toleranceRead ∧
                                        UnaryHistory sternRead ∧
                                          UnaryHistory densityRead ∧
                                            UnaryHistory rationalRead ∧
                                              UnaryHistory windowRead ∧
                                                UnaryHistory regseqRead ∧
                                                  UnaryHistory approxRead ∧
                                                    UnaryHistory sealedRead ∧
                                                      UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier boundaryRoute levelRoute toleranceRoute sternRoute densityRoute rationalRoute
    windowRoute regseqRoute approxRoute sealedRoute namedRoute provenancePkg namePkg
  obtain ⟨bUnary, aUnary, mUnary, lUnary, _tUnary, sUnary, dUnary, qUnary, wUnary,
    rUnary, gUnary, eUnary, hUnary, _cUnary, _pUnary, _nUnary, _aEmpty, _sEmpty,
    _mEmpty, _gEmpty, _eEmpty, _carrierPkg⟩ := carrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed bUnary aUnary boundaryRoute
  have levelUnary : UnaryHistory levelRead :=
    unary_cont_closed boundaryUnary mUnary levelRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed levelUnary lUnary toleranceRoute
  have sternUnary : UnaryHistory sternRead :=
    unary_cont_closed toleranceUnary sUnary sternRoute
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed sternUnary dUnary densityRoute
  have rationalUnary : UnaryHistory rationalRead :=
    unary_cont_closed densityUnary qUnary rationalRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed rationalUnary wUnary windowRoute
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed windowUnary rUnary regseqRoute
  have approxUnary : UnaryHistory approxRead :=
    unary_cont_closed regseqUnary gUnary approxRoute
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed approxUnary eUnary sealedRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealedUnary hUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row boundaryRead ∨ hsame row levelRead ∨ hsame row toleranceRead ∨
              hsame row sternRead ∨ hsame row densityRead ∨ hsame row rationalRead ∨
                hsame row windowRead ∨ hsame row regseqRead ∨ hsame row approxRead ∨
                  hsame row sealedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont windowRead R regseqRead ∧
              Cont regseqRead G approxRead ∧ Cont approxRead E sealedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
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
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, regseqRoute, approxRoute, sealedRoute, provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, boundaryUnary, levelUnary, toleranceUnary, sternUnary, densityUnary,
      rationalUnary, windowUnary, regseqUnary, approxUnary, sealedUnary, namedUnary⟩

end BEDC.Derived.FareySequenceUp
