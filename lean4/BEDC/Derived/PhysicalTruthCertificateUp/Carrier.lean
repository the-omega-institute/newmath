import BEDC.Derived.PhysicalTruthCertificateUp.TasteGate
import BEDC.FKernel.Unary

namespace BEDC.Derived.PhysicalTruthCertificateUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def PhysicalTruthCertificateCarrier (S F O D I L R H C P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  UnaryHistory S ∧ UnaryHistory F ∧ UnaryHistory O ∧ UnaryHistory D ∧
    UnaryHistory I ∧ UnaryHistory L ∧ UnaryHistory R ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ Cont S F R ∧
        Cont R I C ∧ Cont C P N

end BEDC.Derived.PhysicalTruthCertificateUp
