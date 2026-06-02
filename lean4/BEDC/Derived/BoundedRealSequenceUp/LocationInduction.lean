import BEDC.Derived.BoundedRealSequenceUp.NameCertObligations

namespace BEDC.Derived.BoundedRealSequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedRealSequenceCarrier_location_induction [AskSetup] [PackageSetup]
    {S W Q R I H C P N emptyPrefix successorRead readbackRead sealRead boundRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NameCertObligations.BoundedRealSequenceCarrier S W Q R I H C P N bundle pkg →
      hsame emptyPrefix I →
        Cont S W successorRead →
          Cont successorRead Q readbackRead →
            Cont readbackRead R sealRead →
              Cont sealRead I boundRead →
                PkgSig bundle boundRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row boundRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row I ∨ hsame row successorRead ∨ hsame row readbackRead ∨
                          hsame row sealRead ∨ hsame row boundRead)
                      (fun row : BHist =>
                        hsame row boundRead ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle boundRead pkg)
                      hsame ∧
                    hsame emptyPrefix I ∧ UnaryHistory successorRead ∧
                      UnaryHistory readbackRead ∧ UnaryHistory sealRead ∧
                        UnaryHistory boundRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier emptySame successorRoute readbackRoute sealRoute boundRoute boundPkg
  obtain ⟨SUnary, WUnary, QUnary, RUnary, IUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _intervalRoute, _transportSame, carrierPkg, _localCertPkg⟩ := carrier
  have successorUnary : UnaryHistory successorRead :=
    unary_cont_closed SUnary WUnary successorRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed successorUnary QUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary RUnary sealRoute
  have boundUnary : UnaryHistory boundRead :=
    unary_cont_closed sealUnary IUnary boundRoute
  have sourceBound :
      (fun row : BHist => hsame row boundRead ∧ UnaryHistory row) boundRead := by
    exact ⟨hsame_refl boundRead, boundUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row successorRead ∨ hsame row readbackRead ∨
              hsame row sealRead ∨ hsame row boundRead)
          (fun row : BHist =>
            hsame row boundRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle boundRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundRead sourceBound
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, carrierPkg, boundPkg⟩
  }
  exact
    ⟨cert, emptySame, successorUnary, readbackUnary, sealUnary, boundUnary⟩

end BEDC.Derived.BoundedRealSequenceUp
