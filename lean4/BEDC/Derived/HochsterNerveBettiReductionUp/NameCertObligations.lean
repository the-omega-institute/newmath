import BEDC.Derived.HochsterNerveBettiReductionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HochsterNerveBettiReductionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HochsterNerveBettiReductionCarrier [AskSetup] [PackageSetup]
    (V F N H0 B0 G T P L : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory V ∧ UnaryHistory F ∧ UnaryHistory N ∧ UnaryHistory H0 ∧ UnaryHistory B0 ∧
    UnaryHistory G ∧ UnaryHistory T ∧ UnaryHistory P ∧ UnaryHistory L ∧
      PkgSig bundle P pkg ∧ PkgSig bundle L pkg

theorem HochsterNerveBettiReductionNameCertObligations [AskSetup] [PackageSetup]
    {V F N H0 B0 G T P L supportRead faceRead homologyRead bettiRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HochsterNerveBettiReductionCarrier V F N H0 B0 G T P L bundle pkg →
      Cont V F supportRead →
        Cont supportRead N faceRead →
          Cont faceRead H0 homologyRead →
            Cont homologyRead B0 bettiRead →
              PkgSig bundle P pkg →
                PkgSig bundle L pkg →
                  SemanticNameCert
                    (fun row : BHist => hsame row bettiRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row V ∨ hsame row F ∨ hsame row N ∨ hsame row H0 ∨
                        hsame row B0 ∨ hsame row G ∨ hsame row T ∨ hsame row P ∨
                          hsame row L ∨ hsame row bettiRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont V F supportRead ∧
                        Cont supportRead N faceRead ∧ Cont faceRead H0 homologyRead ∧
                          Cont homologyRead B0 bettiRead ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle L pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier supportRoute faceRoute homologyRoute bettiRoute provenancePkg namePkg
  obtain ⟨vUnary, fUnary, nUnary, h0Unary, b0Unary, _gUnary, _tUnary, _pUnary, _lUnary,
    _carrierProvenancePkg, _carrierNamePkg⟩ := carrier
  have supportUnary : UnaryHistory supportRead :=
    unary_cont_closed vUnary fUnary supportRoute
  have faceUnary : UnaryHistory faceRead :=
    unary_cont_closed supportUnary nUnary faceRoute
  have homologyUnary : UnaryHistory homologyRead :=
    unary_cont_closed faceUnary h0Unary homologyRoute
  have bettiUnary : UnaryHistory bettiRead :=
    unary_cont_closed homologyUnary b0Unary bettiRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro bettiRead ⟨hsame_refl bettiRead, bettiUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, supportRoute, faceRoute, homologyRoute, bettiRoute, provenancePkg,
          namePkg⟩
  }

end BEDC.Derived.HochsterNerveBettiReductionUp
