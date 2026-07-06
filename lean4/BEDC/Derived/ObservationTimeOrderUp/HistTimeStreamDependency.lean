import BEDC.Derived.ObservationTimeOrderUp.NameCertObligations

namespace BEDC.Derived.ObservationTimeOrderUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem ObservationTimeOrderHistTimeStreamDependency
    {O0 O1 R C G H P N retainedRead : BHist} :
    UnaryHistory O0 ->
      UnaryHistory O1 ->
        Cont O0 O1 retainedRead ->
          SemanticNameCert
              (fun row : BHist => hsame row retainedRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row O0 ∨ hsame row O1 ∨ hsame row R ∨ hsame row C ∨
                  hsame row G ∨ hsame row H ∨ hsame row P ∨ hsame row N ∨
                    hsame row retainedRead)
              (fun row : BHist => UnaryHistory row ∧ Cont O0 O1 retainedRead)
              hsame ∧
            UnaryHistory retainedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro unaryO0 unaryO1 retainedRoute
  have retainedUnary : UnaryHistory retainedRead :=
    unary_cont_closed unaryO0 unaryO1 retainedRoute
  have sourceRetained :
      (fun row : BHist => hsame row retainedRead ∧ UnaryHistory row) retainedRead := by
    exact ⟨hsame_refl retainedRead, retainedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row retainedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row O0 ∨ hsame row O1 ∨ hsame row R ∨ hsame row C ∨
              hsame row G ∨ hsame row H ∨ hsame row P ∨ hsame row N ∨
                hsame row retainedRead)
          (fun row : BHist => UnaryHistory row ∧ Cont O0 O1 retainedRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro retainedRead sourceRetained
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
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left)))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, retainedRoute⟩
    }
  exact ⟨cert, retainedUnary⟩

theorem ObservationTimeOrderHistTimeStream_field_package_consumer
    {O0 O1 R C G H P N retainedRead : BHist} :
    UnaryHistory O0 ->
      UnaryHistory O1 ->
        Cont O0 O1 retainedRead ->
          SemanticNameCert
              (fun row : BHist =>
                hsame row O0 ∨ hsame row O1 ∨ hsame row R ∨ hsame row C ∨
                  hsame row G ∨ hsame row H ∨ hsame row P ∨ hsame row N)
              (fun row : BHist =>
                hsame row O0 ∨ hsame row O1 ∨ hsame row R ∨ hsame row C ∨
                  hsame row G ∨ hsame row H ∨ hsame row P ∨ hsame row N)
              (fun row : BHist =>
                hsame row O0 ∨ hsame row O1 ∨ hsame row R ∨ hsame row C ∨
                  hsame row G ∨ hsame row H ∨ hsame row P ∨ hsame row N)
              hsame ∧
            SemanticNameCert
                (fun row : BHist => hsame row retainedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row O0 ∨ hsame row O1 ∨ hsame row R ∨ hsame row C ∨
                    hsame row G ∨ hsame row H ∨ hsame row P ∨ hsame row N ∨
                      hsame row retainedRead)
                (fun row : BHist => UnaryHistory row ∧ Cont O0 O1 retainedRead)
                hsame ∧
              UnaryHistory retainedRead := by
  intro unaryO0 unaryO1 retainedRoute
  have fieldPackage :=
    observation_time_order_name_cert_obligations_field_package O0 O1 R C G H P N
  have retainedPackage :=
    ObservationTimeOrderHistTimeStreamDependency
      (O0 := O0)
      (O1 := O1)
      (R := R)
      (C := C)
      (G := G)
      (H := H)
      (P := P)
      (N := N)
      (retainedRead := retainedRead)
      unaryO0
      unaryO1
      retainedRoute
  exact ⟨fieldPackage.left, retainedPackage.left, retainedPackage.right⟩

end BEDC.Derived.ObservationTimeOrderUp
