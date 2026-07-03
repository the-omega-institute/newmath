import BEDC.Derived.ApophaticFiberFarEndUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.ApophaticFiberFarEndUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

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

end BEDC.Derived.ApophaticFiberFarEndUp
