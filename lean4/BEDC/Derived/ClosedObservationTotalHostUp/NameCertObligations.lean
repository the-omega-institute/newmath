import BEDC.Derived.ClosedObservationTotalHostUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ClosedObservationTotalHostUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ClosedObservationTotalHostCarrier [AskSetup] [PackageSetup]
    (A T S F R H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory A ∧ UnaryHistory T ∧ UnaryHistory S ∧ UnaryHistory F ∧ UnaryHistory R ∧
    UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
      PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem ClosedObservationTotalHostNameCertObligations [AskSetup] [PackageSetup]
    {A T S F R H C P N acceptedRead totalRead substrateRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedObservationTotalHostCarrier A T S F R H C P N bundle pkg →
      Cont A T acceptedRead →
        Cont acceptedRead S totalRead →
          Cont totalRead R substrateRead →
            PkgSig bundle P pkg →
              PkgSig bundle N pkg →
                SemanticNameCert
                  (fun row : BHist => hsame row substrateRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row A ∨ hsame row T ∨ hsame row S ∨ hsame row F ∨
                      hsame row R ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                        hsame row N ∨ hsame row substrateRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont A T acceptedRead ∧
                      Cont acceptedRead S totalRead ∧ Cont totalRead R substrateRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier acceptedRoute totalRoute substrateRoute provenancePkg namePkg
  obtain ⟨aUnary, tUnary, sUnary, _fUnary, rUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    _carrierProvenancePkg, _carrierNamePkg⟩ := carrier
  have acceptedUnary : UnaryHistory acceptedRead :=
    unary_cont_closed aUnary tUnary acceptedRoute
  have totalUnary : UnaryHistory totalRead :=
    unary_cont_closed acceptedUnary sUnary totalRoute
  have substrateUnary : UnaryHistory substrateRead :=
    unary_cont_closed totalUnary rUnary substrateRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro substrateRead ⟨hsame_refl substrateRead, substrateUnary⟩
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
      exact ⟨source.right, acceptedRoute, totalRoute, substrateRoute, provenancePkg, namePkg⟩
  }

end BEDC.Derived.ClosedObservationTotalHostUp
