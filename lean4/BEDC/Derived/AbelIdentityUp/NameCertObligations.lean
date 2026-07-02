import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AbelIdentityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def AbelIdentityCarrier [AskSetup] [PackageSetup]
    (Q D W I S R E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory Q ∧ UnaryHistory D ∧ UnaryHistory W ∧ UnaryHistory I ∧
    UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg

theorem AbelIdentityCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {Q D W I S R E H C P N readback : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    AbelIdentityCarrier Q D W I S R E H C P N bundle pkg ->
      Cont Q D W ->
        Cont W I readback ->
          PkgSig bundle readback pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row readback ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row Q ∨ hsame row D ∨ hsame row W ∨ hsame row I ∨
                    hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
                      hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row readback)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont Q D W ∧ Cont W I readback ∧
                    PkgSig bundle readback pkg)
                hsame ∧ UnaryHistory Q ∧ UnaryHistory D ∧ UnaryHistory W ∧
              UnaryHistory I ∧ UnaryHistory readback := by
  -- BEDC touchpoint anchor: AbelIdentityCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier coefficientDerivative wronskianIntegrating readbackPkg
  obtain ⟨qUnary, dUnary, wUnary, iUnary, _sUnary, _rUnary, _eUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _provenancePkg⟩ := carrier
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed wUnary iUnary wronskianIntegrating
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readback ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row D ∨ hsame row W ∨ hsame row I ∨
              hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row readback)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q D W ∧ Cont W I readback ∧
              PkgSig bundle readback pkg)
          hsame := by
    refine
      { core :=
          { carrier_inhabited := ?_
            equiv_refl := ?_
            equiv_symm := ?_
            equiv_trans := ?_
            carrier_respects_equiv := ?_ }
        pattern_sound := ?_
        ledger_sound := ?_ }
    · exact ⟨readback, hsame_refl readback, readbackUnary⟩
    · intro row _source
      exact hsame_refl row
    · intro _row _other sameRows
      exact hsame_symm sameRows
    · intro _row _middle _other sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro _row _other sameRows source
      exact
        ⟨hsame_trans (hsame_symm sameRows) source.left,
          unary_transport source.right sameRows⟩
    · intro _row source
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
    · intro _row source
      exact ⟨source.right, coefficientDerivative, wronskianIntegrating, readbackPkg⟩
  exact ⟨cert, qUnary, dUnary, wUnary, iUnary, readbackUnary⟩

end BEDC.Derived.AbelIdentityUp
