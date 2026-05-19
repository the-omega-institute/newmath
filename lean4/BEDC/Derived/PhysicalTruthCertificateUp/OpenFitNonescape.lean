import BEDC.Derived.PhysicalTruthCertificateUp.TasteGate
import BEDC.FKernel.Unary

namespace BEDC.Derived.PhysicalTruthCertificateUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem PhysicalTruthCertificate_open_fit_nonescape
    {S F O D I L R H C P N fitRead ledgerRead endpoint : BHist} :
    UnaryHistory S →
      UnaryHistory F →
        UnaryHistory L →
          UnaryHistory R →
            Cont S F fitRead →
              Cont L R ledgerRead →
                Cont fitRead ledgerRead endpoint →
                  physicalTruthCertificateFields
                    (PhysicalTruthCertificateUp.mk S F O D I L R H C P N) =
                      [S, F, O, D, I, L, R, H, C, P, N] ∧
                    UnaryHistory fitRead ∧ UnaryHistory ledgerRead ∧
                      UnaryHistory endpoint ∧ Cont S F fitRead ∧ Cont L R ledgerRead ∧
                        Cont fitRead ledgerRead endpoint ∧ hsame endpoint endpoint := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro sourceUnary fitUnary ledgerUnary failureUnary fitRoute ledgerRoute endpointRoute
  have fitReadUnary : UnaryHistory fitRead :=
    unary_cont_closed sourceUnary fitUnary fitRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed ledgerUnary failureUnary ledgerRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed fitReadUnary ledgerReadUnary endpointRoute
  exact
    ⟨rfl, fitReadUnary, ledgerReadUnary, endpointUnary, fitRoute, ledgerRoute,
      endpointRoute, hsame_refl endpoint⟩

end BEDC.Derived.PhysicalTruthCertificateUp
