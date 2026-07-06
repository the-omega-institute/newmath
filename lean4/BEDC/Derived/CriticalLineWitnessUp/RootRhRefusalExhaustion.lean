import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_rh_refusal_exhaustion
    {Z S M R Q H C P N zeroStripRead modulusRead refusalRead rhBoundary consumerRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroStripRead ->
        Cont M R modulusRead ->
          Cont N Q refusalRead ->
            Cont zeroStripRead refusalRead rhBoundary ->
              Cont rhBoundary C consumerRead ->
                SemanticNameCert
                    (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
                        hsame row Q ∨ hsame row N ∨ hsame row zeroStripRead ∨
                          hsame row modulusRead ∨ hsame row refusalRead ∨
                            hsame row rhBoundary ∨ hsame row consumerRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont Z S zeroStripRead ∧
                        Cont M R modulusRead ∧ Cont N Q refusalRead ∧
                          Cont zeroStripRead refusalRead rhBoundary ∧
                            Cont rhBoundary C consumerRead)
                    hsame ∧
                  UnaryHistory zeroStripRead ∧ UnaryHistory modulusRead ∧
                    UnaryHistory refusalRead ∧ UnaryHistory rhBoundary ∧
                      UnaryHistory consumerRead ∧ hsame H (append Z S) ∧ Cont M R Q ∧
                        Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: CriticalLineWitnessCarrier BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroStripRoute modulusRoute refusalRoute boundaryRoute consumerRoute
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
  have unaryZeroStrip : UnaryHistory zeroStripRead :=
    unary_cont_closed unaryZ unaryS zeroStripRoute
  have unaryModulus : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have unaryRefusal : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have unaryBoundary : UnaryHistory rhBoundary :=
    unary_cont_closed unaryZeroStrip unaryRefusal boundaryRoute
  have unaryConsumer : UnaryHistory consumerRead :=
    unary_cont_closed unaryBoundary unaryC consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
              hsame row N ∨ hsame row zeroStripRead ∨ hsame row modulusRead ∨
                hsame row refusalRead ∨ hsame row rhBoundary ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Z S zeroStripRead ∧ Cont M R modulusRead ∧
              Cont N Q refusalRead ∧ Cont zeroStripRead refusalRead rhBoundary ∧
                Cont rhBoundary C consumerRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead
        ⟨hsame_refl consumerRead, unaryConsumer⟩
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
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, zeroStripRoute, modulusRoute, refusalRoute, boundaryRoute,
          consumerRoute⟩
  }
  exact
    ⟨cert, unaryZeroStrip, unaryModulus, unaryRefusal, unaryBoundary, unaryConsumer, sameH,
      routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
