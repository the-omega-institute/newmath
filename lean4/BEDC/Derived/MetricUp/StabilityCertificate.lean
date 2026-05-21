import BEDC.Derived.MetricUp

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem MetricStabilityCertificate_packet_rows {x y d transport provenance ledger : BHist} :
    MetricDistanceWitness x y d →
      Cont d provenance ledger →
        UnaryHistory transport →
          UnaryHistory ledger →
            UnaryHistory d ∧ Cont d provenance ledger ∧
              MetricDistanceWitness x y d ∧ hsame d d := by
  -- BEDC touchpoint anchor: BHist Cont hsame MetricDistanceWitness
  intro witness route _transportRow _ledgerRow
  exact And.intro witness.right.right.left
    (And.intro route (And.intro witness (hsame_refl d)))

end BEDC.Derived.MetricUp
