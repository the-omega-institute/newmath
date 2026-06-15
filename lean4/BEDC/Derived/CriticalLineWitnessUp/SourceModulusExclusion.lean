import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.Package

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_source_modulus_exclusion [AskSetup] [PackageSetup]
    {Z S M R Q H C P N sourceRead modulusRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) Q sourceRead ->
        Cont sourceRead M modulusRead ->
          Cont modulusRead N boundaryRead ->
            PkgSig bundle boundaryRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
                      hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                        hsame row N ∨ hsame row sourceRead ∨
                          hsame row modulusRead ∨ hsame row boundaryRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont (append Z S) Q sourceRead ∧
                      Cont sourceRead M modulusRead ∧ Cont modulusRead N boundaryRead ∧
                        PkgSig bundle boundaryRead pkg)
                  hsame ∧
                UnaryHistory sourceRead ∧ UnaryHistory modulusRead ∧
                  UnaryHistory boundaryRead ∧ hsame H (append Z S) ∧ Cont M R Q ∧
                    Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute modulusRoute boundaryRoute boundaryPkg
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have appendUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport appendUnary (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed appendUnary unaryQ sourceRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed sourceUnary unaryM modulusRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed modulusUnary unaryN boundaryRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row sourceRead ∨ hsame row modulusRead ∨ hsame row boundaryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont (append Z S) Q sourceRead ∧
              Cont sourceRead M modulusRead ∧ Cont modulusRead N boundaryRead ∧
                PkgSig bundle boundaryRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro boundaryRead ⟨hsame_refl boundaryRead, boundaryUnary⟩
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
                          (Or.inr (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sourceRoute, modulusRoute, boundaryRoute, boundaryPkg⟩
  }
  exact
    ⟨cert, sourceUnary, modulusUnary, boundaryUnary, sameH, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
