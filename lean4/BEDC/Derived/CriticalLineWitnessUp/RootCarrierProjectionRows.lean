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

theorem CriticalLineWitnessRootCarrierProjectionRows [AskSetup] [PackageSetup]
    {Z S M R Q H C P N rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S (append Z S) ->
        Cont M R (append M R) ->
          Cont Q H rootRead ->
            PkgSig bundle P pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
                      hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                        hsame row N ∨ hsame row rootRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont Z S (append Z S) ∧
                      Cont M R (append M R) ∧ Cont Q H rootRead ∧
                        PkgSig bundle P pkg)
                  hsame ∧
                Cont Z S (append Z S) ∧ Cont M R (append M R) ∧
                  Cont Q H rootRead := by
  -- BEDC touchpoint anchor: CriticalLineWitnessCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute modulusRoute rootRoute provenancePkg
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have sourceUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have modulusUnary : UnaryHistory (append M R) :=
    unary_cont_closed unaryM unaryR modulusRoute
  have unaryH : UnaryHistory H :=
    unary_transport sourceUnary (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have _unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed unaryQ unaryH rootRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row rootRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Z S (append Z S) ∧ Cont M R (append M R) ∧
              Cont Q H rootRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rootRead ⟨hsame_refl rootRead, rootUnary⟩
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
      right; right; right; right; right; right; right; right; right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sourceRoute, modulusRoute, rootRoute, provenancePkg⟩
  }
  exact ⟨cert, sourceRoute, modulusRoute, rootRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
