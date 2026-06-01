import BEDC.Derived.FareySequenceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceRefinementCoverage [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N levelRead mediantRead toleranceRead
      sternRead windowRead regularRead approximationRead sealRead coveredRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg ->
      Cont B A levelRead ->
        Cont levelRead M mediantRead ->
          Cont mediantRead L toleranceRead ->
            Cont toleranceRead T sternRead ->
              Cont sternRead S windowRead ->
                Cont windowRead R regularRead ->
                  Cont regularRead G approximationRead ->
                    Cont approximationRead E sealRead ->
                      Cont sealRead H coveredRead ->
                        PkgSig bundle P pkg ->
                          PkgSig bundle N pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row coveredRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row B ∨ hsame row A ∨ hsame row M ∨
                                    hsame row L ∨ hsame row T ∨ hsame row S ∨
                                      hsame row W ∨ hsame row R ∨ hsame row G ∨
                                        hsame row E ∨ hsame row H ∨ hsame row coveredRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont B A levelRead ∧
                                    Cont levelRead M mediantRead ∧
                                      Cont mediantRead L toleranceRead ∧
                                        Cont toleranceRead T sternRead ∧
                                          Cont sternRead S windowRead ∧
                                            Cont windowRead R regularRead ∧
                                              Cont regularRead G approximationRead ∧
                                                Cont approximationRead E sealRead ∧
                                                  Cont sealRead H coveredRead ∧
                                                    PkgSig bundle P pkg ∧
                                                      PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory levelRead ∧ UnaryHistory mediantRead ∧
                                UnaryHistory toleranceRead ∧ UnaryHistory sternRead ∧
                                  UnaryHistory windowRead ∧ UnaryHistory regularRead ∧
                                    UnaryHistory approximationRead ∧ UnaryHistory sealRead ∧
                                      UnaryHistory coveredRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier levelRoute mediantRoute toleranceRoute sternRoute windowRoute regularRoute
    approximationRoute sealRoute coveredRoute packageP packageN
  obtain ⟨bUnary, aUnary, mUnary, lUnary, tUnary, sUnary, _dUnary, _qUnary,
    _wUnary, rUnary, gUnary, eUnary, hUnary, _cUnary, _pUnary, _nUnary,
    _aEmpty, _sEmpty, _mEmpty, _gEmpty, _eEmpty, _provenancePkg⟩ := carrier
  have levelUnary : UnaryHistory levelRead :=
    unary_cont_closed bUnary aUnary levelRoute
  have mediantUnary : UnaryHistory mediantRead :=
    unary_cont_closed levelUnary mUnary mediantRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed mediantUnary lUnary toleranceRoute
  have sternUnary : UnaryHistory sternRead :=
    unary_cont_closed toleranceUnary tUnary sternRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sternUnary sUnary windowRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed windowUnary rUnary regularRoute
  have approximationUnary : UnaryHistory approximationRead :=
    unary_cont_closed regularUnary gUnary approximationRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed approximationUnary eUnary sealRoute
  have coveredUnary : UnaryHistory coveredRead :=
    unary_cont_closed sealUnary hUnary coveredRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row coveredRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row L ∨ hsame row T ∨
              hsame row S ∨ hsame row W ∨ hsame row R ∨ hsame row G ∨ hsame row E ∨
                hsame row H ∨ hsame row coveredRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B A levelRead ∧ Cont levelRead M mediantRead ∧
              Cont mediantRead L toleranceRead ∧ Cont toleranceRead T sternRead ∧
                Cont sternRead S windowRead ∧ Cont windowRead R regularRead ∧
                  Cont regularRead G approximationRead ∧ Cont approximationRead E sealRead ∧
                    Cont sealRead H coveredRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro coveredRead ⟨hsame_refl coveredRead, coveredUnary⟩
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
        ⟨source.right, levelRoute, mediantRoute, toleranceRoute, sternRoute, windowRoute,
          regularRoute, approximationRoute, sealRoute, coveredRoute, packageP, packageN⟩
  }
  exact
    ⟨cert, levelUnary, mediantUnary, toleranceUnary, sternUnary, windowUnary, regularUnary,
      approximationUnary, sealUnary, coveredUnary⟩

end BEDC.Derived.FareySequenceUp
