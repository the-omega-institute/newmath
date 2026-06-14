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

theorem CriticalLineWitnessCarrier_namecert_root_unblock_consumer_scope [AskSetup]
    [PackageSetup] {Z S M R Q H C P N stripRead modulusRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S stripRead ->
        Cont stripRead Q modulusRead ->
          Cont modulusRead N consumerRead ->
            PkgSig bundle consumerRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row stripRead ∨ hsame row modulusRead ∨
                      hsame row consumerRead ∨ hsame row N)
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle consumerRead pkg)
                  hsame ∧
                UnaryHistory stripRead ∧ UnaryHistory modulusRead ∧
                  UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro packet stripRoute modulusRoute consumerRoute pkgSig
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
  have unaryStrip : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  have unaryModulus : UnaryHistory modulusRead :=
    unary_cont_closed unaryStrip unaryQ modulusRoute
  have unaryConsumer : UnaryHistory consumerRead :=
    unary_cont_closed unaryModulus unaryN consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stripRead ∨ hsame row modulusRead ∨ hsame row consumerRead ∨
              hsame row N)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead ⟨hsame_refl consumerRead, unaryConsumer⟩
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
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, pkgSig⟩
  }
  exact ⟨cert, unaryStrip, unaryModulus, unaryConsumer⟩

end BEDC.Derived.CriticalLineWitnessUp
