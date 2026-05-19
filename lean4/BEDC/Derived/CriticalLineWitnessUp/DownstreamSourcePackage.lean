import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_downstream_source_package
    {Z S M R Q H C P N sourceRead ledgerRead downstreamRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont Z S sourceRead →
        Cont M R ledgerRead →
          Cont sourceRead ledgerRead downstreamRead →
            SemanticNameCert
                (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row downstreamRead ∧ Cont Z S sourceRead ∧ Cont M R ledgerRead)
                (fun row : BHist =>
                  hsame row downstreamRead ∧ Cont sourceRead ledgerRead downstreamRead)
                hsame ∧
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                UnaryHistory Q ∧ UnaryHistory sourceRead ∧ UnaryHistory ledgerRead ∧
                  UnaryHistory downstreamRead ∧ hsame H (append Z S) ∧
                    Cont Z S sourceRead ∧ Cont M R Q ∧ Cont M R ledgerRead ∧
                      Cont sourceRead ledgerRead downstreamRead ∧ Cont Q H C ∧
                        Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute ledgerRoute downstreamRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed unaryM unaryR ledgerRoute
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed sourceUnary ledgerUnary downstreamRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row downstreamRead ∧ Cont Z S sourceRead ∧ Cont M R ledgerRead)
          (fun row : BHist =>
            hsame row downstreamRead ∧ Cont sourceRead ledgerRead downstreamRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro downstreamRead ⟨hsame_refl downstreamRead, downstreamUnary⟩
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
      exact ⟨source.left, sourceRoute, ledgerRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, downstreamRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, sourceUnary, ledgerUnary,
      downstreamUnary, sameH, sourceRoute, routeQ, ledgerRoute, downstreamRoute, routeC,
      routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
