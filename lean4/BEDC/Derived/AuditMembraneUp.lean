import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.AuditMembraneUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def AuditMembraneCarrier (G B R D H P N : BHist) : Prop :=
  UnaryHistory G ∧ UnaryHistory B ∧ UnaryHistory D ∧ UnaryHistory P ∧
    hsame H (append G B) ∧ Cont G B R ∧ Cont R D N

theorem AuditMembraneCarrier_refusal_replay_closure {G B R D H P N : BHist} :
    AuditMembraneCarrier G B R D H P N →
      UnaryHistory R ∧ UnaryHistory N ∧ hsame H (append G B) := by
  intro packet
  have unaryG : UnaryHistory G :=
    packet.left
  have unaryB : UnaryHistory B :=
    packet.right.left
  have unaryD : UnaryHistory D :=
    packet.right.right.left
  have sameAuditFace : hsame H (append G B) :=
    packet.right.right.right.right.left
  have refusalRoute : Cont G B R :=
    packet.right.right.right.right.right.left
  have replayRoute : Cont R D N :=
    packet.right.right.right.right.right.right
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryG unaryB refusalRoute
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryR unaryD replayRoute
  exact ⟨unaryR, unaryN, sameAuditFace⟩

theorem AuditMembraneCarrier_drift_resolution {G B R D H P N drift : BHist} :
    AuditMembraneCarrier G B R D H P N →
      Cont D P drift →
        UnaryHistory D ∧ UnaryHistory P ∧ UnaryHistory drift ∧ Cont D P drift ∧
          hsame H (append G B) ∧ Cont R D N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet driftRoute
  have unaryD : UnaryHistory D :=
    packet.right.right.left
  have unaryP : UnaryHistory P :=
    packet.right.right.right.left
  have sameAuditFace : hsame H (append G B) :=
    packet.right.right.right.right.left
  have replayRoute : Cont R D N :=
    packet.right.right.right.right.right.right
  have unaryDrift : UnaryHistory drift :=
    unary_cont_closed unaryD unaryP driftRoute
  exact ⟨unaryD, unaryP, unaryDrift, driftRoute, sameAuditFace, replayRoute⟩

end BEDC.Derived.AuditMembraneUp
