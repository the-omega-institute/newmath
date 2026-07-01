import BEDC.Derived.BoundedRegularCauchyUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BoundedRegularCauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BoundedRegularCauchyCarrier [AskSetup] [PackageSetup]
    (S M B Q A H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory B ∧ UnaryHistory Q ∧
    UnaryHistory A ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem BoundedRegularCauchyCarrier_tail_window_induction [AskSetup] [PackageSetup]
    {S M B Q A H C P N thresholdRead boundRead readbackRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedRegularCauchyCarrier S M B Q A H C P N bundle pkg ->
      Cont M S thresholdRead ->
        Cont thresholdRead B boundRead ->
          Cont boundRead Q readbackRead ->
            Cont readbackRead A sealRead ->
              PkgSig bundle sealRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row M ∨ hsame row S ∨ hsame row B ∨ hsame row Q ∨
                        hsame row A ∨ hsame row thresholdRead ∨ hsame row boundRead ∨
                          hsame row readbackRead ∨ hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont M S thresholdRead ∧
                        Cont thresholdRead B boundRead ∧ Cont boundRead Q readbackRead ∧
                          Cont readbackRead A sealRead ∧ PkgSig bundle sealRead pkg)
                    hsame ∧
                  UnaryHistory thresholdRead ∧ UnaryHistory boundRead ∧
                    UnaryHistory readbackRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier thresholdRoute boundRoute readbackRoute sealRoute sealPkg
  obtain ⟨sUnary, mUnary, bUnary, qUnary, aUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    _pPkg, _nPkg⟩ := carrier
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed mUnary sUnary thresholdRoute
  have boundUnary : UnaryHistory boundRead :=
    unary_cont_closed thresholdUnary bUnary boundRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed boundUnary qUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary aUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row S ∨ hsame row B ∨ hsame row Q ∨ hsame row A ∨
              hsame row thresholdRead ∨ hsame row boundRead ∨ hsame row readbackRead ∨
                hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M S thresholdRead ∧ Cont thresholdRead B boundRead ∧
              Cont boundRead Q readbackRead ∧ Cont readbackRead A sealRead ∧
                PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := ⟨sealRead, hsame_refl sealRead, sealUnary⟩
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
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, thresholdRoute, boundRoute, readbackRoute, sealRoute, sealPkg⟩
  }
  exact ⟨cert, thresholdUnary, boundUnary, readbackUnary, sealUnary⟩

end BEDC.Derived.BoundedRegularCauchyUp
