import BEDC.Derived.ClosedNormalConsistencyMainUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ClosedNormalConsistencyMainUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedNormalConsistencyMainNameCertObligations [AskSetup] [PackageSetup]
    {T L B F R H C P N routeRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T →
      UnaryHistory L →
        UnaryHistory B →
          UnaryHistory F →
            UnaryHistory R →
              UnaryHistory H →
                UnaryHistory C →
                  UnaryHistory P →
                    UnaryHistory N →
                      Cont T L routeRead →
                        Cont routeRead B R →
                          Cont R C publicRead →
                            PkgSig bundle P pkg →
                              PkgSig bundle N pkg →
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row publicRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row T ∨ hsame row L ∨ hsame row B ∨
                                        hsame row F ∨ hsame row R ∨ hsame row H ∨
                                          hsame row C ∨ hsame row P ∨ hsame row N ∨
                                            hsame row publicRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont T L routeRead ∧
                                        Cont routeRead B R ∧ Cont R C publicRead ∧
                                          PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                    hsame ∧
                                  UnaryHistory routeRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro tUnary lUnary bUnary _fUnary _rUnary _hUnary cUnary _pUnary _nUnary
    endpointRoute contradictionRoute publicRoute provenancePkg namePkg
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed tUnary lUnary endpointRoute
  have contradictionUnary : UnaryHistory R :=
    unary_cont_closed routeUnary bUnary contradictionRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed contradictionUnary cUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row L ∨ hsame row B ∨ hsame row F ∨
              hsame row R ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T L routeRead ∧ Cont routeRead B R ∧
              Cont R C publicRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead
        ⟨hsame_refl publicRead, publicUnary⟩
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
      exact
        ⟨source.right, endpointRoute, contradictionRoute, publicRoute, provenancePkg,
          namePkg⟩
  }
  exact ⟨cert, routeUnary, publicUnary⟩

end BEDC.Derived.ClosedNormalConsistencyMainUp
