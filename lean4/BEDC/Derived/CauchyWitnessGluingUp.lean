import BEDC.Derived.CauchyWitnessGluingUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyWitnessGluingUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def CauchyWitnessGluingCarrier
    (ledger tail synchronizer classifier stream regular dyadic realSeal edge transport route
      provenance localName : BHist) : Prop :=
  UnaryHistory ledger ∧ UnaryHistory tail ∧ UnaryHistory synchronizer ∧
    UnaryHistory classifier ∧ UnaryHistory stream ∧ UnaryHistory regular ∧
      UnaryHistory dyadic ∧ UnaryHistory realSeal ∧ UnaryHistory edge ∧
        UnaryHistory transport ∧ Cont ledger tail edge ∧ Cont synchronizer classifier route ∧
          Cont stream dyadic regular ∧ Cont regular realSeal edge ∧
            hsame transport (append edge route)

theorem CauchyWitnessGluingCarrier_route_obligation_surface
    {ledger tail synchronizer classifier stream regular dyadic realSeal edge transport route
      provenance localName : BHist} :
    CauchyWitnessGluingCarrier ledger tail synchronizer classifier stream regular dyadic realSeal
        edge transport route provenance localName ->
      UnaryHistory ledger ∧ UnaryHistory tail ∧ UnaryHistory synchronizer ∧
        UnaryHistory classifier ∧ UnaryHistory stream ∧ UnaryHistory regular ∧
          UnaryHistory dyadic ∧ UnaryHistory realSeal ∧ UnaryHistory edge ∧
            UnaryHistory transport ∧ Cont ledger tail edge ∧ Cont synchronizer classifier route ∧
              Cont stream dyadic regular ∧ Cont regular realSeal edge ∧
                hsame transport (append edge route) := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro carrier
  obtain
    ⟨ledgerUnary, tailUnary, synchronizerUnary, classifierUnary, streamUnary, regularUnary,
      dyadicUnary, realSealUnary, edgeUnary, transportUnary, ledgerTailEdge,
      synchronizerClassifierRoute, streamDyadicRegular, regularRealSealEdge,
      transportRoute⟩ := carrier
  exact
    ⟨ledgerUnary, tailUnary, synchronizerUnary, classifierUnary, streamUnary, regularUnary,
      dyadicUnary, realSealUnary, edgeUnary, transportUnary, ledgerTailEdge,
      synchronizerClassifierRoute, streamDyadicRegular, regularRealSealEdge, transportRoute⟩

end BEDC.Derived.CauchyWitnessGluingUp
