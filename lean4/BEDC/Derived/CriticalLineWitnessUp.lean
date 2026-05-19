import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def CriticalLineWitnessCarrier (Z S M R Q H C P N : BHist) : Prop :=
  UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory P ∧
    hsame H (append Z S) ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N

theorem CriticalLineWitnessCarrier_modulus_route_closure {Z S M R Q H C P N : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) := by
  intro packet
  have unaryZ : UnaryHistory Z :=
    packet.left
  have unaryS : UnaryHistory S :=
    packet.right.left
  have unaryM : UnaryHistory M :=
    packet.right.right.left
  have unaryR : UnaryHistory R :=
    packet.right.right.right.left
  have unaryP : UnaryHistory P :=
    packet.right.right.right.right.left
  have sameH : hsame H (append Z S) :=
    packet.right.right.right.right.right.left
  have routeQ : Cont M R Q :=
    packet.right.right.right.right.right.right.left
  have routeC : Cont Q H C :=
    packet.right.right.right.right.right.right.right.left
  have routeN : Cont C P N :=
    packet.right.right.right.right.right.right.right.right
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  exact ⟨unaryQ, unaryC, unaryN, sameH⟩

theorem CriticalLineWitnessCarrier_modulus_depth_route_determinacy
    {Z S M R Q H C P N Qp Cp : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont M R Qp ->
        Cont Qp H Cp ->
          hsame Cp C ->
            hsame Qp Q ∧ UnaryHistory Qp ∧ UnaryHistory Cp ∧ hsame H (append Z S) := by
  intro packet routeQp routeCp _sameCp
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, _routeC, _routeN⟩ :=
    packet
  have sameQp : hsame Qp Q :=
    cont_deterministic routeQp routeQ
  have unaryQp : UnaryHistory Qp :=
    unary_cont_closed unaryM unaryR routeQp
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryCp : UnaryHistory Cp :=
    unary_cont_closed unaryQp unaryH routeCp
  exact ⟨sameQp, unaryQp, unaryCp, sameH⟩

theorem CriticalLineWitnessCarrier_root_source_triad {Z S M R Q H C P N : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ hsame H (append Z S) ∧
        Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  exact
    ⟨packet.left, packet.right.left, routeClosure.left, routeClosure.right.right.right,
      packet.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right⟩

theorem CriticalLineWitnessRhNonescapePackage {Z S M R Q H C P N refusalRead rhRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont N Q refusalRead ->
        Cont refusalRead C rhRead ->
          SemanticNameCert
              (fun row : BHist => hsame row rhRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row rhRead)
              (fun row : BHist => hsame row rhRead ∧ Cont refusalRead C rhRead)
              hsame ∧
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
              UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧
                UnaryHistory refusalRead ∧ UnaryHistory rhRead ∧ hsame H (append Z S) ∧
                  Cont M R Q ∧ Cont Q H C ∧ Cont C P N ∧ Cont N Q refusalRead ∧
                    Cont refusalRead C rhRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet refusalRoute rhRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC _unaryP routeN
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have rhUnary : UnaryHistory rhRead :=
    unary_cont_closed refusalUnary unaryC rhRoute
  have sourceAtRh : hsame rhRead rhRead ∧ UnaryHistory rhRead :=
    ⟨hsame_refl rhRead, rhUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rhRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row rhRead)
          (fun row : BHist => hsame row rhRead ∧ Cont refusalRead C rhRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rhRead sourceAtRh
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
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, rhRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryC, unaryN, refusalUnary, rhUnary,
      sameH, routeQ, routeC, routeN, refusalRoute, rhRoute⟩

theorem CriticalLineWitnessCarrier_zero_strip_carrier_totality {Z S M R Q H C P N : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory Q ∧
        UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) ∧ Cont M R Q ∧
          Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, _sameH, routeQ, routeC, routeN⟩ :=
    packet
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, routeClosure.left, routeClosure.right.left,
      routeClosure.right.right.left, routeClosure.right.right.right, routeQ, routeC, routeN⟩

theorem CriticalLineWitnessCarrier_fixed_strip_window_surface
    {Z S M R Q H C P N stripRead refusalRead realWindow : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N -> Cont Z S stripRead ->
      Cont N Q refusalRead -> Cont M R realWindow ->
        UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
          UnaryHistory Q ∧ UnaryHistory stripRead ∧ UnaryHistory refusalRead ∧
            UnaryHistory realWindow ∧ hsame H (append Z S) ∧ Cont Z S stripRead ∧
              Cont N Q refusalRead ∧ Cont M R realWindow ∧ Cont M R Q ∧
                Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet stripRoute refusalRoute realRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryN : UnaryHistory N :=
    routeClosure.right.right.left
  have unaryStrip : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  have unaryRefusal : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have unaryReal : UnaryHistory realWindow :=
    unary_cont_closed unaryM unaryR realRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryStrip, unaryRefusal, unaryReal,
      sameH, stripRoute, refusalRoute, realRoute, routeQ, routeC, routeN⟩

theorem CriticalLineWitnessCarrier_zero_strip_modulus_package_exhaustion
    {Z S M R Q H C P N zetaRead modulusRead downstream : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaRead ->
        Cont zetaRead Q modulusRead ->
          Cont N Q downstream ->
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
              UnaryHistory Q ∧ UnaryHistory zetaRead ∧ UnaryHistory modulusRead ∧
                UnaryHistory downstream ∧ hsame H (append Z S) ∧ Cont Z S zetaRead ∧
                  Cont zetaRead Q modulusRead ∧ Cont M R Q ∧ Cont Q H C ∧
                    Cont C P N ∧ Cont N Q downstream := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet zeroStripRoute modulusRoute downstreamRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryZetaRead : UnaryHistory zetaRead :=
    unary_cont_closed unaryZ unaryS zeroStripRoute
  have unaryModulusRead : UnaryHistory modulusRead :=
    unary_cont_closed unaryZetaRead unaryQ modulusRoute
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC _unaryP routeN
  have unaryDownstream : UnaryHistory downstream :=
    unary_cont_closed unaryN unaryQ downstreamRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryZetaRead, unaryModulusRead,
      unaryDownstream, sameH, zeroStripRoute, modulusRoute, routeQ, routeC, routeN,
      downstreamRoute⟩

theorem CriticalLineWitnessCarrier_root_zeta_source_obligation
    {Z S M R Q H C P N zetaRead sourceRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaRead ->
        Cont zetaRead H sourceRead ->
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory H ∧
            UnaryHistory zetaRead ∧ UnaryHistory sourceRead ∧ hsame H (append Z S) ∧
              Cont Z S zetaRead ∧ Cont zetaRead H sourceRead ∧ Cont M R Q ∧
                Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet zetaRoute sourceRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryZetaRead : UnaryHistory zetaRead :=
    unary_cont_closed unaryZ unaryS zetaRoute
  have unarySourceRead : UnaryHistory sourceRead :=
    unary_cont_closed unaryZetaRead unaryH sourceRoute
  exact
    ⟨unaryZ, unaryS, routeClosure.left, unaryH, unaryZetaRead, unarySourceRead, sameH,
      zetaRoute, sourceRoute, routeQ, routeC, routeN⟩

theorem CriticalLineWitnessCarrier_root_dependency_scope
    {Z S M R Q H C P N zetaRead depthRead ledgerRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaRead ->
        Cont M Q depthRead ->
          Cont depthRead H ledgerRead ->
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
              UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory N ∧
                UnaryHistory zetaRead ∧ UnaryHistory depthRead ∧ UnaryHistory ledgerRead ∧
                  hsame H (append Z S) ∧ Cont Z S zetaRead ∧ Cont M R Q ∧
                    Cont M Q depthRead ∧ Cont depthRead H ledgerRead ∧ Cont Q H C ∧
                      Cont C P N := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet zetaRoute depthRoute ledgerRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryZetaRead : UnaryHistory zetaRead :=
    unary_cont_closed unaryZ unaryS zetaRoute
  have unaryDepthRead : UnaryHistory depthRead :=
    unary_cont_closed unaryM routeClosure.left depthRoute
  have unaryLedgerRead : UnaryHistory ledgerRead :=
    unary_cont_closed unaryDepthRead unaryH ledgerRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, routeClosure.left, unaryH, routeClosure.right.left,
      routeClosure.right.right.left, unaryZetaRead, unaryDepthRead, unaryLedgerRead, sameH,
      zetaRoute, routeQ, depthRoute, ledgerRoute, routeC, routeN⟩

theorem CriticalLineWitnessCarrier_root_unblock_modulus_ledger
    {Z S M R Q H C P N depthRead modulusRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont M R depthRead →
        Cont depthRead H modulusRead →
          UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory depthRead ∧
            UnaryHistory modulusRead ∧ hsame H (append Z S) ∧ Cont M R Q ∧
              Cont M R depthRead ∧ Cont depthRead H modulusRead ∧ Cont Q H C ∧
                Cont C P N := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet depthRoute modulusRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have depthUnary : UnaryHistory depthRead :=
    unary_cont_closed unaryM unaryR depthRoute
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed depthUnary unaryH modulusRoute
  exact
    ⟨unaryM,
      unaryR,
      depthUnary,
      modulusUnary,
      sameH,
      routeQ,
      depthRoute,
      modulusRoute,
      routeC,
      routeN⟩

theorem CriticalLineWitnessCarrier_downstream_zero_source_readback
    {Z S M R Q H C P N zeroRead downstreamRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroRead ->
        Cont zeroRead Q downstreamRead ->
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory zeroRead ∧
            UnaryHistory downstreamRead ∧ hsame H (append Z S) ∧ Cont Z S zeroRead ∧
              Cont zeroRead Q downstreamRead ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet zeroRoute downstreamRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have zeroReadUnary : UnaryHistory zeroRead :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have downstreamReadUnary : UnaryHistory downstreamRead :=
    unary_cont_closed zeroReadUnary unaryQ downstreamRoute
  exact
    ⟨unaryZ, unaryS, unaryQ, zeroReadUnary, downstreamReadUnary, sameH, zeroRoute,
      downstreamRoute, routeQ, routeC, routeN⟩

theorem CriticalLineWitnessCarrier_root_fixed_tuple_image_row
    {Z S M R Q H C P N image : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) Q image ->
        UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
          UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory image ∧ hsame H (append Z S) ∧
            Cont M R Q ∧ Cont Q H C ∧ Cont C P N ∧ Cont (append Z S) Q image := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet imageRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have sourceUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport sourceUnary (hsame_symm sameH)
  have imageUnary : UnaryHistory image :=
    unary_cont_closed sourceUnary unaryQ imageRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, imageUnary, sameH, routeQ,
      routeC, routeN, imageRoute⟩

theorem CriticalLineWitnessCarrier_root_unblock_refusal_boundary
    {Z S M R Q H C P N refusalRead boundaryRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont N Q refusalRead ->
        Cont refusalRead C boundaryRead ->
          SemanticNameCert
              (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row boundaryRead)
              (fun row : BHist => hsame row boundaryRead ∧ Cont refusalRead C boundaryRead)
              hsame ∧
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
              UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧
                UnaryHistory refusalRead ∧ UnaryHistory boundaryRead ∧ hsame H (append Z S) ∧
                  Cont M R Q ∧ Cont Q H C ∧ Cont C P N ∧ Cont N Q refusalRead ∧
                    Cont refusalRead C boundaryRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet refusalRoute boundaryRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC _unaryP routeN
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed refusalUnary unaryC boundaryRoute
  have sourceAtBoundary : hsame boundaryRead boundaryRead ∧ UnaryHistory boundaryRead :=
    ⟨hsame_refl boundaryRead, boundaryUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row boundaryRead)
          (fun row : BHist => hsame row boundaryRead ∧ Cont refusalRead C boundaryRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundaryRead sourceAtBoundary
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
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, boundaryRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryC, unaryN, refusalUnary,
      boundaryUnary, sameH, routeQ, routeC, routeN, refusalRoute, boundaryRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
