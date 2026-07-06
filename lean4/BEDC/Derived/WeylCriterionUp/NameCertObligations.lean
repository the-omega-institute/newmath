import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.WeylCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def WeylCriterionCarrier [AskSetup] [PackageSetup]
    (I F Z U S R D E H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory I ∧ UnaryHistory F ∧ UnaryHistory Z ∧ UnaryHistory U ∧
    UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory E ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        PkgSig bundle P pkg

theorem WeylCriterionNameCertObligations [AskSetup] [PackageSetup]
    {I F Z U S R D E H C P N sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WeylCriterionCarrier I F Z U S R D E H C P N bundle pkg ->
      Cont C E sealRead ->
        PkgSig bundle N pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row N ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row I ∨ hsame row F ∨ hsame row Z ∨ hsame row U ∨
                  hsame row S ∨ hsame row R ∨ hsame row D ∨ hsame row E ∨
                    hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
              (fun row : BHist => UnaryHistory row ∧ Cont C E sealRead ∧ PkgSig bundle N pkg)
              hsame ∧
            UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier sealRoute namePkg
  obtain ⟨_iUnary, _fUnary, _zUnary, _uUnary, _sUnary, _rUnary, _dUnary, eUnary,
    _hUnary, cUnary, _pUnary, nUnary, _provenancePkg⟩ := carrier
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed cUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row F ∨ hsame row Z ∨ hsame row U ∨
              hsame row S ∨ hsame row R ∨ hsame row D ∨ hsame row E ∨
                hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist => UnaryHistory row ∧ Cont C E sealRead ∧ PkgSig bundle N pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro N ⟨hsame_refl N, nUnary⟩
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
          intro row other sameRows source
          have otherSame : hsame other N :=
            hsame_trans (hsame_symm sameRows) source.left
          have otherUnary : UnaryHistory other :=
            unary_transport source.right sameRows
          exact ⟨otherSame, otherUnary⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, sealRoute, namePkg⟩
    }
  exact ⟨cert, sealUnary⟩

theorem WeylCriterionCarrier_equidistribution_route [AskSetup] [PackageSetup]
    {I F Z U S R D E H C P N phaseRead averageRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WeylCriterionCarrier I F Z U S R D E H C P N bundle pkg ->
      Cont I F phaseRead ->
        Cont U S averageRead ->
          Cont phaseRead averageRead Z ->
            Cont Z R D ->
              Cont D E sealRead ->
                PkgSig bundle sealRead pkg ->
                  UnaryHistory phaseRead ∧ UnaryHistory averageRead ∧
                    UnaryHistory sealRead ∧ Cont I F phaseRead ∧
                      Cont U S averageRead ∧ Cont phaseRead averageRead Z ∧
                        Cont Z R D ∧ Cont D E sealRead ∧
                          PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro carrier phaseCont averageCont phaseAverageCont zeroReadCont sealCont sealPkg
  obtain ⟨iUnary, fUnary, _zUnary, uUnary, sUnary, _rUnary, dUnary, eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _provenancePkg⟩ := carrier
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed iUnary fUnary phaseCont
  have averageUnary : UnaryHistory averageRead :=
    unary_cont_closed uUnary sUnary averageCont
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dUnary eUnary sealCont
  exact
    ⟨phaseUnary, averageUnary, sealUnary, phaseCont, averageCont, phaseAverageCont,
      zeroReadCont, sealCont, sealPkg⟩

end BEDC.Derived.WeylCriterionUp
