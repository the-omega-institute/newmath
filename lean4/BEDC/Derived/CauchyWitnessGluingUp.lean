import BEDC.Derived.CauchyWitnessGluingUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyWitnessGluingUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem CauchyWitnessGluingCarrier_witness_ledger_semantic_name_certificate
    {ledger tail synchronizer classifier stream regular dyadic realSeal edge transport route
      provenance localName ledgerRead : BHist} :
    CauchyWitnessGluingCarrier ledger tail synchronizer classifier stream regular dyadic realSeal
        edge transport route provenance localName ->
      Cont edge route ledgerRead ->
        SemanticNameCert
            (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
            (fun row : BHist => hsame row ledgerRead)
            (fun row : BHist => hsame row ledgerRead ∧ Cont edge route ledgerRead)
            hsame ∧
          UnaryHistory ledger ∧ UnaryHistory tail ∧ UnaryHistory synchronizer ∧
            UnaryHistory classifier ∧ UnaryHistory edge ∧ UnaryHistory route ∧
              UnaryHistory ledgerRead ∧ Cont ledger tail edge ∧
                Cont synchronizer classifier route ∧ Cont edge route ledgerRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier edgeRouteLedgerRead
  obtain
    ⟨ledgerUnary, tailUnary, synchronizerUnary, classifierUnary, _streamUnary,
      _regularUnary, _dyadicUnary, _realSealUnary, edgeUnary, _transportUnary,
      ledgerTailEdge, synchronizerClassifierRoute, _streamDyadicRegular,
      _regularRealSealEdge, _transportRoute⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed synchronizerUnary classifierUnary synchronizerClassifierRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed edgeUnary routeUnary edgeRouteLedgerRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row ledgerRead)
          (fun row : BHist => hsame row ledgerRead ∧ Cont edge route ledgerRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ledgerRead
        (And.intro (hsame_refl ledgerRead) ledgerReadUnary)
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
          And.intro (hsame_trans (hsame_symm sameRows) source.left)
            (unary_transport source.right sameRows)
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact And.intro source.left edgeRouteLedgerRead
  }
  exact
    ⟨cert, ledgerUnary, tailUnary, synchronizerUnary, classifierUnary, edgeUnary, routeUnary,
      ledgerReadUnary, ledgerTailEdge, synchronizerClassifierRoute, edgeRouteLedgerRead⟩

end BEDC.Derived.CauchyWitnessGluingUp
