import BEDC.FKernel.Unary

namespace BEDC.Derived.ModulusOfConvergenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def ModulusOfConvergencePacket
    (precision threshold modulus schedule late ledger provenance : BHist) : Prop :=
  UnaryHistory precision ∧ UnaryHistory threshold ∧ UnaryHistory schedule ∧
    UnaryHistory late ∧ Cont precision threshold modulus ∧ Cont schedule late ledger ∧
      Cont modulus ledger provenance

theorem ModulusOfConvergencePacket_ledger_exactness
    {precision threshold modulus schedule late ledger provenance : BHist} :
    ModulusOfConvergencePacket precision threshold modulus schedule late ledger provenance ->
      UnaryHistory precision ∧ UnaryHistory threshold ∧ UnaryHistory schedule ∧
        UnaryHistory late ∧ UnaryHistory modulus ∧ UnaryHistory ledger ∧
          UnaryHistory provenance ∧ hsame modulus (append precision threshold) ∧
            hsame ledger (append schedule late) ∧
              hsame provenance (append modulus ledger) := by
  intro packet
  have precisionUnary : UnaryHistory precision := packet.left
  have thresholdUnary : UnaryHistory threshold := packet.right.left
  have scheduleUnary : UnaryHistory schedule := packet.right.right.left
  have lateUnary : UnaryHistory late := packet.right.right.right.left
  have modulusCont : Cont precision threshold modulus := packet.right.right.right.right.left
  have ledgerCont : Cont schedule late ledger := packet.right.right.right.right.right.left
  have provenanceCont : Cont modulus ledger provenance := packet.right.right.right.right.right.right
  have modulusUnary : UnaryHistory modulus :=
    unary_cont_closed precisionUnary thresholdUnary modulusCont
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed scheduleUnary lateUnary ledgerCont
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed modulusUnary ledgerUnary provenanceCont
  constructor
  · exact precisionUnary
  constructor
  · exact thresholdUnary
  constructor
  · exact scheduleUnary
  constructor
  · exact lateUnary
  constructor
  · exact modulusUnary
  constructor
  · exact ledgerUnary
  constructor
  · exact provenanceUnary
  constructor
  · exact modulusCont
  constructor
  · exact ledgerCont
  · exact provenanceCont

end BEDC.Derived.ModulusOfConvergenceUp
