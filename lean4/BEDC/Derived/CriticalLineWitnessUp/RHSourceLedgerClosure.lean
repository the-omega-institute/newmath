import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_rh_source_ledger_closure
    {Z S M R Q H C P N sourceRead modulusRead refusalRead publicRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont M R modulusRead ->
          Cont N Q refusalRead ->
            Cont sourceRead modulusRead publicRead ->
              SemanticNameCert
                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row publicRead ∧ Cont Z S sourceRead ∧
                      Cont M R modulusRead)
                  (fun row : BHist =>
                    hsame row publicRead ∧ Cont N Q refusalRead ∧
                      Cont sourceRead modulusRead publicRead)
                  hsame ∧
                UnaryHistory sourceRead ∧ UnaryHistory modulusRead ∧
                  UnaryHistory refusalRead ∧ UnaryHistory publicRead ∧
                    hsame H (append Z S) ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute modulusRoute refusalRoute publicRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed routeClosure.right.right.left routeClosure.left refusalRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sourceUnary modulusUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row publicRead ∧ Cont Z S sourceRead ∧ Cont M R modulusRead)
          (fun row : BHist =>
            hsame row publicRead ∧ Cont N Q refusalRead ∧
              Cont sourceRead modulusRead publicRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact ⟨source.left, sourceRoute, modulusRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, refusalRoute, publicRoute⟩
  }
  exact
    ⟨cert, sourceUnary, modulusUnary, refusalUnary, publicUnary, sameH, routeQ, routeC,
      routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
