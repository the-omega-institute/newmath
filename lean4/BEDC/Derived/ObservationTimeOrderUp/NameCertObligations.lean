import BEDC.Derived.ObservationTimeOrderUp.TasteGate

namespace BEDC.Derived.ObservationTimeOrderUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem observation_time_order_name_cert_obligations_field_package
    (O0 O1 R C G H P N : BHist) :
    SemanticNameCert
        (fun row : BHist =>
          hsame row O0 ∨ hsame row O1 ∨ hsame row R ∨ hsame row C ∨ hsame row G ∨
            hsame row H ∨ hsame row P ∨ hsame row N)
        (fun row : BHist =>
          hsame row O0 ∨ hsame row O1 ∨ hsame row R ∨ hsame row C ∨ hsame row G ∨
            hsame row H ∨ hsame row P ∨ hsame row N)
        (fun row : BHist =>
          hsame row O0 ∨ hsame row O1 ∨ hsame row R ∨ hsame row C ∨ hsame row G ∨
            hsame row H ∨ hsame row P ∨ hsame row N)
        hsame ∧
      observationTimeOrderFields (ObservationTimeOrderUp.mk O0 O1 R C G H P N) =
        [O0, O1, R, C, G, H, P, N] := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert NameCert
  have base := ObservationTimeOrderNo_host_time_nonescape O0 O1 R C G H P N
  exact ⟨NameCert_carrier_self_semantic_lifting base.left, base.right⟩

theorem observation_time_order_erasure_boundary_gap_semantic_consumer
    {O0 O1 R C G H P N recordRead retainedRead gapRead : BHist} :
    UnaryHistory O0 →
      UnaryHistory O1 →
        UnaryHistory R →
          UnaryHistory G →
            Cont O0 O1 recordRead →
              Cont recordRead R retainedRead →
                Cont retainedRead G gapRead →
                  observationTimeOrderFromEventFlow
                      (observationTimeOrderToEventFlow
                        (ObservationTimeOrderUp.mk O0 O1 R C G H P N)) =
                    some (ObservationTimeOrderUp.mk O0 O1 R C G H P N) →
                    SemanticNameCert
                        (fun row : BHist => hsame row gapRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          (hsame row gapRead ∧ UnaryHistory row) ∨
                            ObservationTimeOrderObligationRowSpec O0 O1 R C G H P N row)
                        (fun row : BHist =>
                          UnaryHistory row ∧
                            Cont retainedRead G gapRead ∧
                              hsame
                                (observationTimeOrderDecodeBHist
                                  (observationTimeOrderEncodeBHist G))
                                G)
                        hsame ∧
                      UnaryHistory gapRead := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert UnaryHistory
  intro sourceUnary targetUnary retainedUnary gapUnary sourceRoute retainedRoute gapRoute readback
  have boundary :=
    ObservationTimeOrderErasureBoundary_gap_route sourceUnary targetUnary retainedUnary gapUnary
      sourceRoute retainedRoute gapRoute readback
  have gapReadUnary : UnaryHistory gapRead := boundary.right.right.left
  have gapExact :
      hsame
        (observationTimeOrderDecodeBHist (observationTimeOrderEncodeBHist G))
        G := boundary.right.right.right
  have sourceGap :
      (fun row : BHist => hsame row gapRead ∧ UnaryHistory row) gapRead := by
    exact ⟨hsame_refl gapRead, gapReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row gapRead ∧ UnaryHistory row)
          (fun row : BHist =>
            (hsame row gapRead ∧ UnaryHistory row) ∨
              ObservationTimeOrderObligationRowSpec O0 O1 R C G H P N row)
          (fun row : BHist =>
            UnaryHistory row ∧
              Cont retainedRead G gapRead ∧
                hsame
                  (observationTimeOrderDecodeBHist (observationTimeOrderEncodeBHist G))
                  G)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro gapRead sourceGap
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
        exact Or.inl source
      ledger_sound := by
        intro _row source
        exact ⟨source.right, gapRoute, gapExact⟩
    }
  exact ⟨cert, gapReadUnary⟩

end BEDC.Derived.ObservationTimeOrderUp
