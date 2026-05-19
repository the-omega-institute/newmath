import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_fixed_strip_zero_route_boundary
    {Z S M R Q H C P N zeroRead modulusRead rhBoundary : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroRead ->
        Cont zeroRead Q modulusRead ->
          Cont modulusRead C rhBoundary ->
            SemanticNameCert
                (fun row : BHist => hsame row rhBoundary ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row rhBoundary ∧ Cont Z S zeroRead ∧
                    Cont zeroRead Q modulusRead)
                (fun row : BHist =>
                  hsame row rhBoundary ∧ Cont modulusRead C rhBoundary)
                hsame ∧
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory C ∧
                UnaryHistory zeroRead ∧ UnaryHistory modulusRead ∧
                  UnaryHistory rhBoundary ∧ hsame H (append Z S) ∧
                    Cont Z S zeroRead ∧ Cont zeroRead Q modulusRead ∧
                      Cont modulusRead C rhBoundary ∧ Cont M R Q ∧ Cont Q H C ∧
                        Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroRoute modulusRoute rhRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, sameH, routeQ, routeC,
    routeN⟩ := packet
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed zeroUnary routeClosure.left modulusRoute
  have rhUnary : UnaryHistory rhBoundary :=
    unary_cont_closed modulusUnary routeClosure.right.left rhRoute
  have sourceAtBoundary : hsame rhBoundary rhBoundary ∧ UnaryHistory rhBoundary :=
    ⟨hsame_refl rhBoundary, rhUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row rhBoundary ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row rhBoundary ∧ Cont Z S zeroRead ∧ Cont zeroRead Q modulusRead)
        (fun row : BHist => hsame row rhBoundary ∧ Cont modulusRead C rhBoundary)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro rhBoundary sourceAtBoundary
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
      exact ⟨source.left, zeroRoute, modulusRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, rhRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, routeClosure.left, routeClosure.right.left, zeroUnary,
      modulusUnary, rhUnary, sameH, zeroRoute, modulusRoute, rhRoute, routeQ, routeC,
      routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
