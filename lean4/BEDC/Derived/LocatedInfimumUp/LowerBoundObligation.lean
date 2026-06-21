import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedInfimumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedInfimumLowerBoundObligation [AskSetup] [PackageSetup]
    {F L G W R E H C P N lowerRead windowRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory F ∧ UnaryHistory L ∧ UnaryHistory G ∧ UnaryHistory W ∧
      UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧
        UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg) ->
      Cont F L lowerRead ->
        Cont W R windowRead ->
          Cont windowRead E sealRead ->
            Cont sealRead N namedRead ->
              PkgSig bundle namedRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row F ∨ hsame row L ∨ hsame row W ∨ hsame row R ∨
                        hsame row E ∨ hsame row N ∨ hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont F L lowerRead ∧ Cont W R windowRead ∧
                        Cont windowRead E sealRead ∧ Cont sealRead N namedRead ∧
                          PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
                    hsame ∧
                  UnaryHistory lowerRead ∧ UnaryHistory windowRead ∧
                    UnaryHistory sealRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier lowerRoute windowRoute sealRoute namedRoute namedPkg
  obtain
    ⟨fUnary, lUnary, _gUnary, wUnary, rUnary, eUnary, _hUnary, _cUnary,
      _pUnary, nUnary, provenancePkg⟩ := carrier
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed fUnary lUnary lowerRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary rUnary windowRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary eUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nUnary namedRoute
  have sourceNamed :
      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row) namedRead := by
    exact ⟨hsame_refl namedRead, namedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row L ∨ hsame row W ∨ hsame row R ∨
              hsame row E ∨ hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F L lowerRead ∧ Cont W R windowRead ∧
              Cont windowRead E sealRead ∧ Cont sealRead N namedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead sourceNamed
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, lowerRoute, windowRoute, sealRoute, namedRoute, provenancePkg,
          namedPkg⟩
  }
  exact ⟨cert, lowerUnary, windowUnary, sealUnary, namedUnary⟩

end BEDC.Derived.LocatedInfimumUp
