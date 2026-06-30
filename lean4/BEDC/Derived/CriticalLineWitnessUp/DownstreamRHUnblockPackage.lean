import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_downstream_rh_unblock_package
    {Z S M R Q H C P N sourceRead refusalRead downstreamRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont N Q refusalRead ->
          Cont sourceRead refusalRead downstreamRead ->
            SemanticNameCert
                (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
                    hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                      hsame row N ∨ hsame row sourceRead ∨ hsame row refusalRead ∨
                        hsame row downstreamRead)
                (fun row : BHist =>
                  hsame row downstreamRead ∧ Cont Z S sourceRead ∧
                    Cont N Q refusalRead ∧ Cont sourceRead refusalRead downstreamRead)
                hsame ∧
              UnaryHistory sourceRead ∧ UnaryHistory refusalRead ∧
                UnaryHistory downstreamRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute refusalRoute downstreamRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have unarySource : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have unaryRefusal : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have unaryDownstream : UnaryHistory downstreamRead :=
    unary_cont_closed unarySource unaryRefusal downstreamRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
              hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row sourceRead ∨ hsame row refusalRead ∨
                  hsame row downstreamRead)
          (fun row : BHist =>
            hsame row downstreamRead ∧ Cont Z S sourceRead ∧
              Cont N Q refusalRead ∧ Cont sourceRead refusalRead downstreamRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro downstreamRead
        ⟨hsame_refl downstreamRead, unaryDownstream⟩
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
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, sourceRoute, refusalRoute, downstreamRoute⟩
  }
  exact ⟨cert, unarySource, unaryRefusal, unaryDownstream⟩

end BEDC.Derived.CriticalLineWitnessUp
