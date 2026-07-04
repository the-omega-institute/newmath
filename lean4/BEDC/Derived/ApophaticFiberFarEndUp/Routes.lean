import BEDC.Derived.ApophaticFiberFarEndUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ApophaticFiberFarEndUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem ApophaticFiberFarEnd_noninternality
    (x : ApophaticFiberFarEndUp) :
    ∃ socket fiber ledger boundary inscription transport route provenance name socketRead fiberRead
        boundaryRead localRead : BHist,
      x =
          ApophaticFiberFarEndUp.mk socket fiber ledger boundary inscription transport route
            provenance name ∧
        Cont socket fiber socketRead ∧
          Cont fiber ledger fiberRead ∧
            Cont ledger boundary boundaryRead ∧
              Cont boundary inscription localRead ∧
                apophaticFiberFarEndFromEventFlow
                    (apophaticFiberFarEndToEventFlow x) =
                  some x := by
  -- BEDC touchpoint anchor: BHist BMark Cont
  cases x with
  | mk socket fiber ledger boundary inscription transport route provenance name =>
      exact
        ⟨socket, fiber, ledger, boundary, inscription, transport, route, provenance, name,
          append socket fiber, append fiber ledger, append ledger boundary,
          append boundary inscription, rfl, rfl, rfl, rfl, rfl,
          ApophaticFiberFarEndTasteGate_single_carrier_alignment.right.left
            (ApophaticFiberFarEndUp.mk socket fiber ledger boundary inscription transport route
              provenance name)⟩

theorem ApophaticFiberFarEnd_ledger_boundary_route
    {socket fiber ledger boundary inscription transport route provenance name socketRead fiberRead
      boundaryRead localRead : BHist} :
    Cont socket fiber socketRead ->
      Cont fiber ledger fiberRead ->
        Cont ledger boundary boundaryRead ->
          Cont boundary inscription localRead ->
            hsame boundaryRead (append ledger boundary) ∧
              hsame localRead (append boundary inscription) ∧
                ∃ x : ApophaticFiberFarEndUp,
                  x =
                      ApophaticFiberFarEndUp.mk socket fiber ledger boundary inscription transport
                        route provenance name ∧
                    apophaticFiberFarEndFromEventFlow
                        (apophaticFiberFarEndToEventFlow x) =
                      some x := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  intro _socketRoute _fiberRoute boundaryRoute inscriptionRoute
  constructor
  · exact boundaryRoute
  · constructor
    · exact inscriptionRoute
    · exact
        ⟨ApophaticFiberFarEndUp.mk socket fiber ledger boundary inscription transport route
            provenance name,
          rfl,
          ApophaticFiberFarEndTasteGate_single_carrier_alignment.right.left
            (ApophaticFiberFarEndUp.mk socket fiber ledger boundary inscription transport route
              provenance name)⟩

theorem ApophaticFiberFarEnd_boundary_ledger_required
    {boundary ledger accepted exported : BHist} :
    Cont boundary ledger exported →
      Cont boundary accepted exported →
        hsame ledger accepted := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  intro ledgerRoute acceptedRoute
  exact cont_left_cancel ledgerRoute acceptedRoute

theorem ApophaticFiberFarEndCarrier_independence_witness
    {socket fiber ledger boundary inscription transport route provenance name : BHist} :
    SemanticNameCert
        (fun row : BHist =>
          hsame row fiber ∨ hsame row ledger ∨ hsame row boundary ∨ hsame row inscription)
        (fun row : BHist =>
          hsame row socket ∨ hsame row fiber ∨ hsame row ledger ∨ hsame row boundary ∨
            hsame row inscription ∨ hsame row transport ∨ hsame row route ∨
              hsame row provenance ∨ hsame row name)
        (fun row : BHist =>
          (hsame row fiber ∨ hsame row ledger ∨ hsame row boundary ∨ hsame row inscription) ∧
            Cont fiber ledger (append fiber ledger) ∧
              Cont ledger boundary (append ledger boundary) ∧
                Cont boundary inscription (append boundary inscription))
        hsame ∧
      Cont fiber ledger (append fiber ledger) ∧
        Cont ledger boundary (append ledger boundary) ∧
          Cont boundary inscription (append boundary inscription) := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame SemanticNameCert
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro fiber (Or.inl (hsame_refl fiber))
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
          intro row other sameRows source
          cases source with
          | inl sameFiber =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameFiber)
          | inr rest =>
              cases rest with
              | inl sameLedger =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameLedger))
              | inr rest =>
                  cases rest with
                  | inl sameBoundary =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inl (hsame_trans (hsame_symm sameRows) sameBoundary)))
                  | inr sameInscription =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inr (hsame_trans (hsame_symm sameRows) sameInscription)))
      }
      pattern_sound := by
        intro row source
        cases source with
        | inl sameFiber =>
            exact Or.inr (Or.inl sameFiber)
        | inr rest =>
            cases rest with
            | inl sameLedger =>
                exact Or.inr (Or.inr (Or.inl sameLedger))
            | inr rest =>
                cases rest with
                | inl sameBoundary =>
                    exact Or.inr (Or.inr (Or.inr (Or.inl sameBoundary)))
                | inr sameInscription =>
                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameInscription))))
      ledger_sound := by
        intro row source
        exact ⟨source, rfl, rfl, rfl⟩
    }
  · exact ⟨rfl, rfl, rfl⟩

end BEDC.Derived.ApophaticFiberFarEndUp
