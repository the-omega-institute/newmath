import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_rh_boundary_refusal
    {Z S M R Q H C P N refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont N Q refusalRead →
        SemanticNameCert
            (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
                hsame row refusalRead)
            (fun row : BHist =>
              UnaryHistory row ∧ Cont N Q refusalRead ∧ hsame H (append Z S))
            hsame ∧
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
            UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ UnaryHistory refusalRead ∧
              hsame H (append Z S) ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N ∧
                Cont N Q refusalRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory CriticalLineWitnessCarrier
  intro packet refusalRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed routeClosure.right.right.left routeClosure.left refusalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
              hsame row refusalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont N Q refusalRead ∧ hsame H (append Z S))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusalRead ⟨hsame_refl refusalRead, refusalUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, refusalRoute, sameH⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, routeClosure.left, routeClosure.right.left,
      routeClosure.right.right.left, refusalUnary, sameH, routeQ, routeC, routeN,
      refusalRoute⟩

theorem CriticalLineWitnessCarrier_rh_boundary_namecert_handoff [AskSetup] [PackageSetup]
    {Z S M R Q H C P N handoff : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont N Q handoff ->
        PkgSig bundle N pkg ->
          PkgSig bundle handoff pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row handoff ∧ UnaryHistory row)
                (fun row : BHist => hsame row handoff ∧ PkgSig bundle N pkg)
                (fun row : BHist =>
                  hsame row handoff ∧ Cont N Q handoff ∧ PkgSig bundle handoff pkg)
                hsame ∧
              UnaryHistory N ∧ UnaryHistory Q ∧ UnaryHistory handoff ∧
                Cont N Q handoff ∧ PkgSig bundle N pkg ∧
                  PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory PkgSig
  intro packet handoffRoute nameSig handoffSig
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed routeClosure.right.right.left routeClosure.left handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoff ∧ UnaryHistory row)
          (fun row : BHist => hsame row handoff ∧ PkgSig bundle N pkg)
          (fun row : BHist =>
            hsame row handoff ∧ Cont N Q handoff ∧ PkgSig bundle handoff pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoff ⟨hsame_refl handoff, handoffUnary⟩
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
      exact ⟨source.left, nameSig⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, handoffRoute, handoffSig⟩
  }
  exact
    ⟨cert, routeClosure.right.right.left, routeClosure.left, handoffUnary, handoffRoute,
      nameSig, handoffSig⟩

end BEDC.Derived.CriticalLineWitnessUp
