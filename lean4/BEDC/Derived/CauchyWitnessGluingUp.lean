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

theorem CauchyWitnessGluingCarrier_scoped_primitive_binding
    {ledger tail synchronizer classifier stream regular dyadic realSeal edge transport route
      provenance localName scopedRead : BHist} :
    CauchyWitnessGluingCarrier ledger tail synchronizer classifier stream regular dyadic realSeal
        edge transport route provenance localName ->
      Cont edge route scopedRead ->
        SemanticNameCert
            (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row edge ∨ hsame row route ∨ hsame row transport ∨ hsame row scopedRead)
            (fun row : BHist => hsame row scopedRead ∧ Cont edge route scopedRead)
            hsame ∧
          UnaryHistory stream ∧ UnaryHistory regular ∧ UnaryHistory dyadic ∧
            UnaryHistory realSeal ∧ UnaryHistory edge ∧ UnaryHistory route ∧
              UnaryHistory transport ∧ UnaryHistory scopedRead ∧
                hsame transport (append edge route) ∧ Cont stream dyadic regular ∧
                  Cont regular realSeal edge ∧ Cont edge route scopedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier edgeRouteScopedRead
  obtain
    ⟨_ledgerUnary, _tailUnary, synchronizerUnary, classifierUnary, streamUnary, regularUnary,
      dyadicUnary, realSealUnary, edgeUnary, transportUnary, _ledgerTailEdge,
      synchronizerClassifierRoute, streamDyadicRegular, regularRealSealEdge,
      transportRoute⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed synchronizerUnary classifierUnary synchronizerClassifierRoute
  have scopedReadUnary : UnaryHistory scopedRead :=
    unary_cont_closed edgeUnary routeUnary edgeRouteScopedRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row edge ∨ hsame row route ∨ hsame row transport ∨ hsame row scopedRead)
          (fun row : BHist => hsame row scopedRead ∧ Cont edge route scopedRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopedRead
        (And.intro (hsame_refl scopedRead) scopedReadUnary)
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact And.intro source.left edgeRouteScopedRead
  }
  exact
    ⟨cert, streamUnary, regularUnary, dyadicUnary, realSealUnary, edgeUnary, routeUnary,
      transportUnary, scopedReadUnary, transportRoute, streamDyadicRegular, regularRealSealEdge,
      edgeRouteScopedRead⟩

end BEDC.Derived.CauchyWitnessGluingUp
