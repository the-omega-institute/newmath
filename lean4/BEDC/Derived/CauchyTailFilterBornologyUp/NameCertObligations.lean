import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyTailFilterBornologyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyTailFilterBornologyCarrier [AskSetup] [PackageSetup]
    (S R B W M E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory B ∧ UnaryHistory W ∧
    UnaryHistory M ∧ UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem CauchyTailFilterBornologyNameCertObligations [AskSetup] [PackageSetup]
    {S R B W M E H C P N tailRead boundRead modulusRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyTailFilterBornologyCarrier S R B W M E H C P N bundle pkg →
      Cont S W tailRead →
        Cont tailRead B boundRead →
          Cont boundRead M modulusRead →
            Cont modulusRead E sealRead →
              PkgSig bundle P pkg →
                PkgSig bundle N pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row S ∨ hsame row R ∨ hsame row B ∨ hsame row W ∨
                          hsame row M ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                            hsame row P ∨ hsame row N ∨ hsame row sealRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont S W tailRead ∧
                          Cont tailRead B boundRead ∧ Cont boundRead M modulusRead ∧
                            Cont modulusRead E sealRead ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle N pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier tailRoute boundRoute modulusRoute sealRoute provenancePkg namePkg
  obtain ⟨sUnary, _rUnary, bUnary, wUnary, mUnary, eUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _carrierProvenancePkg, _carrierNamePkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed sUnary wUnary tailRoute
  have boundUnary : UnaryHistory boundRead :=
    unary_cont_closed tailUnary bUnary boundRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed boundUnary mUnary modulusRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed modulusUnary eUnary sealRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact Or.inr
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
      exact
        ⟨source.right, tailRoute, boundRoute, modulusRoute, sealRoute, provenancePkg,
          namePkg⟩
  }

end BEDC.Derived.CauchyTailFilterBornologyUp
